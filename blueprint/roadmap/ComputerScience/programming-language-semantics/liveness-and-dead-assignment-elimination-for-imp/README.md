# Liveness and dead-assignment elimination for IMP

Live-variables analysis for the while language [IMP](../operational-semantics-of-imp/README.md), computed by recursion on the command rather than on a control-flow graph, its correctness as a simulation property of the [big-step semantics](../operational-semantics-of-imp/big-step.md), and the elimination of assignments to dead variables that it justifies. True liveness refines the analysis so that a variable read only by a dead assignment is dead too.

- [Live variables of an IMP command](live-variables-of-an-imp-command.md)
- [Correctness of live-variables analysis for IMP](correctness-of-live-variables-analysis-for-imp.md)
- [Correctness of dead-assignment elimination](correctness-of-dead-assignment-elimination.md)
- [True liveness of an IMP command](true-liveness-of-an-imp-command.md)
- [Correctness of true liveness](correctness-of-true-liveness.md)
