# Liveness and dead-assignment elimination for IMP

Live-variables analysis for the while language [IMP](../operational-semantics-of-imp/README.md), computed by recursion on the command rather than on a control-flow graph, its correctness as a simulation property of the [big-step semantics](../operational-semantics-of-imp/big-step.md), and the elimination of assignments to dead variables that it justifies. True liveness refines the analysis so that a variable read only by a dead assignment is dead too.

- [Live variables of an IMP command](live-variables-of-an-imp-command.md)
- [Gen and kill sets of an IMP command](gen-and-kill-sets-of-an-imp-command.md)
- [Liveness is a gen/kill analysis](liveness-is-a-gen-kill-analysis.md)
- [Live variables of a loop are closed under its body](live-variables-of-a-loop-are-closed-under-its.md)
- [Coincidence for IMP expressions](coincidence-for-imp-expressions.md)
- [Correctness of live-variables analysis for IMP](correctness-of-live-variables-analysis-for-imp.md)
- [Dead-assignment elimination for IMP](dead-assignment-elimination-for-imp.md)
- [Dead-assignment elimination simulates the source program](dead-assignment-elimination-simulates-the-sour.md)
- [The source program simulates dead-assignment elimination](the-source-program-simulates-dead-assignment-e.md)
- [Correctness of dead-assignment elimination](correctness-of-dead-assignment-elimination.md)
- [True liveness of an IMP command](true-liveness-of-an-imp-command.md)
- [True liveness is monotone](true-liveness-is-monotone.md)
- [Correctness of true liveness](correctness-of-true-liveness.md)
