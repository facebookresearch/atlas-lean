# Loop-free paths of a transition system

Let $T$ be a transition relation on a set of states, $I$ a set of initial states and $P$ a set of states, the property. A sequence of states $s_0, \dots, s_n$ is a *path* of length $n$ if $T(s_i, s_{i+1})$ for all $0 \le i < n$; a path of length $0$ is a single state. It is *loop-free* if moreover $s_i \ne s_j$ for all $0 \le i < j \le n$. Subpaths of loop-free paths are loop-free, and shortest paths between two states are loop-free. The system is *$P$-safe* if every state reachable from $I$ satisfies $P$.

## Sources

- M. Sheeran, S. Singh and G. Stålmarck, "Checking safety properties using induction and a SAT-solver", *Formal Methods in Computer-Aided Design (FMCAD 2000)*, LNCS 1954, Springer, 2000, pp. 108–125, Section 2.1.
