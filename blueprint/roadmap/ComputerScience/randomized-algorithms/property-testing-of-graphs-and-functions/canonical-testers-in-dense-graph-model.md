# Goldreich–Trevisan: canonical testers suffice in the dense graph model

A tester in the dense graph model is *canonical* if it samples a uniformly random set of $s$ vertices, queries all pairs among them, and accepts iff the induced subgraph belongs to a set $\Pi'_n$ of $s$-vertex graphs, which may depend on the number $n$ of vertices of the input graph. Every one-sided tester for a graph property making $q$ queries (adaptive or not) can be converted into a canonical one-sided tester with $2q$ sample vertices, hence $\binom{2q}{2}$ queries, and the same proximity.

## Proof sketch

Each query of the original tester involves at most two new vertices, so its run depends only on the subgraph induced by at most $2q$ vertices; by isomorphism invariance one may relabel these to be a uniformly random set. The canonical tester accepts iff the induced subgraph is an induced subgraph of some $n$-vertex graph in $\Pi$ (so $\Pi'_n$ depends on $n$; with a set independent of $n$ the claim fails, as noted by Goldreich, correcting Goldreich–Trevisan): a one-sided tester can reject only on answers inconsistent with every graph in $\Pi$, so whenever the emulated run rejects the canonical tester rejects too, and graphs in $\Pi$ are always accepted.

## Depends on

- [Property testing in the dense graph model](dense-graph-property-testing-model.md)

## Sources

- O. Goldreich and L. Trevisan, "Three Theorems Regarding Testing Graph Properties", Random Structures & Algorithms 23(1), 2003.
- O. Goldreich, "Introduction to Property Testing", Cambridge University Press, 2017.
