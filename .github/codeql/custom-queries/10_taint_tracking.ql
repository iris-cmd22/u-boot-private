/**
 * @kind path-problem
 */

import cpp
import semmle.code.cpp.dataflow.TaintTracking
import semmle.code.cpp.controlflow.Guards

class NetworkByteSwap extends Expr {
  NetworkByteSwap () {
    // TODO: sostituire <class> e <var>
    exists(MacroInvocation mi |
      // TODO: <condition>
      mi.getMacroName().matches("ntoh%") and mi.getExpr() = this
    )
  }
}

module MyConfig implements DataFlow::ConfigSig {

  predicate isSource(DataFlow::Node source) {
    // TODO
    source.asExpr() instanceof NetworkByteSwap
  }
  predicate isSink(DataFlow::Node sink) {
    // TODO
    exists(FunctionCall fc |
      fc.getTarget().getName() = "memcpy" and
      sink.asExpr() = fc.getArgument(2)
    )
  }

  predicate isBarrier(DataFlow::Node node) {
    exists(GuardCondition gc, Variable v |
      // la guard fa riferimento alla variabile v (es. `if (len > MAX)`)
      gc.(Expr).getAChild*() = v.getAnAccess() and
      // il nodo che valutiamo e' proprio un accesso a v
      node.asExpr() = v.getAnAccess() and
      // il nodo e' raggiungibile solo passando per la guard, cioe' e' "protetto"
      gc.controls(node.asExpr().getBasicBlock(), _) and
      // esclude i controlli che sono in realta' condizioni di loop
      not exists(Loop loop | loop.getControllingExpr() = gc)
    )
  }
}

module MyTaint = TaintTracking::Global<MyConfig>;
import MyTaint::PathGraph

from MyTaint::PathNode source, MyTaint::PathNode sink
where MyTaint::flowPath(source, sink) 
select sink, source, sink, "Network byte swap flows to memcpy"