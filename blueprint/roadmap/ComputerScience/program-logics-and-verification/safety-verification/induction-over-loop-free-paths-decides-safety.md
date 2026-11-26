# Induction over loop-free paths decides safety

Let $T$ be a transition relation on a finite set of states in which every state has a successor, with initial states $I$ and property $P$. For $i = 0, 1, 2, \dots$ check in turn:

1. if no [loop-free path](loop-free-paths-of-a-transition-system.md) of length $i$ starts in $I$, or no loop-free path of length $i$ ends outside $P$, stop with the answer that the system is $P$-safe;
2. if some path of length $i$ from a state in $I$ ends outside $P$, stop and return it as a counterexample.

This procedure terminates and is correct: it answers safe exactly when every state reachable from $I$ satisfies $P$, and otherwise returns a shortest counterexample path. It terminates because a loop-free path visits at most as many states as there are. The restriction to loop-free paths is needed for completeness, since every state has a successor and so paths of every length exist.

## Depends on

- [Loop-free paths of a transition system](loop-free-paths-of-a-transition-system.md)

## Sources

- M. Sheeran, S. Singh and G. Stålmarck, "Checking safety properties using induction and a SAT-solver", *Formal Methods in Computer-Aided Design (FMCAD 2000)*, LNCS 1954, Springer, 2000, pp. 108–125, Section 3, Algorithm 1 and the soundness and completeness argument after it.
