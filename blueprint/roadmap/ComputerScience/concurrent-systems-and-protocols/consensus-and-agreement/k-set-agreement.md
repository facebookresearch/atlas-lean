# k-set agreement

In the $k$-set agreement problem, each process starts with an input. A completed outcome on a finite population records at most one decision at each process. It satisfies three conditions:

- **Validity:** every recorded decision is the input of some process, which need not be correct.
- **Agreement:** at most $k$ distinct decision values are recorded. This counts decisions made by faulty processes as well as those made by correct processes.
- **Termination:** every correct process has a recorded decision.

For $k = 1$, the agreement condition is equivalent to pairwise equality of all recorded decisions, the consensus agreement condition for this choice of whose decisions count. For $k = 0$, no process can decide, so a satisfying outcome has no correct processes. This is a specification of completed outcomes; it does not assert that a protocol terminates or can solve the problem.

## Sources

- S. Chaudhuri, "More choices allow more faults: set consensus problems in totally asynchronous systems", *Information and Computation* 105(1):132–158, 1993
- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>
