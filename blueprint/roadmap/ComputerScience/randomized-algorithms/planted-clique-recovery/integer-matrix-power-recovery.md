# Planted clique recovery by exact integer matrix powers

There is a deterministic algorithm using only exact integer arithmetic (powers of the signed adjacency matrix applied to standard basis vectors, a growth test on squared norms, selection of the largest coordinates and degree cleanup) that, for every planted set $S$ with $|S| \ge 1024\sqrt{n}$, recovers $S$ except on a fraction at most $2e^{-n} + n e^{-|S|/32}$ of the edge coins. It runs in polynomial time on multi-tape Turing machines, uniformly over all runtime values of $n$ and $k$ given in unary with the adjacency bits.

## Proof sketch

Power growth: a column whose power grows fast enough has a large component along the rank-one signal, and the growth test certifies it; the recovered vector inherits the approximation estimate, and the deterministic recovery lemma finishes on the high-probability event.

## Depends on

- [Planted clique model, search and detection problems](../../../GraphTheory/random-graphs/planted-clique/planted-clique-model.md)
- [The complexity class P](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/p.md)

## Proof depends on

- [Deterministic recovery from an approximate signal](planted-clique-deterministic-recovery.md)
- [Spectral norm of planted-clique noise is O(sqrt n)](../../../GraphTheory/random-graphs/planted-clique/planted-clique-noise-spectral-norm.md)
- [Outside vertices have at most 5|S|/8 neighbors in the planted clique](../../../GraphTheory/random-graphs/planted-clique/planted-clique-outside-degrees.md)

## Sources

- N. Alon, M. Krivelevich and B. Sudakov, "Finding a Large Hidden Clique in a Random Graph", Random Structures & Algorithms 13(3-4), 1998.
