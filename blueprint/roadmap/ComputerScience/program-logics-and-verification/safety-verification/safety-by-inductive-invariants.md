# Safety by inductive invariants

Let $(S, I, \to)$ be a transition system and $B \subseteq S$ a set of bad states. A set $J \subseteq S$ is an *invariant* if it contains every state reachable from $I$, and *inductive* if $I \subseteq J$ and $J$ is closed under $\to$. Every inductive set is an invariant, and the set of reachable states is the least inductive set. Hence no bad state is reachable if and only if there is an inductive set disjoint from $B$.

## Depends on

- [Reachability in a labelled transition system is transitive](../../process-calculi/labelled-transition-systems/trans.md)

## Sources

- A. R. Bradley, "SAT-based model checking without unrolling", *VMCAI 2011*, LNCS 6538, Springer, 2011
