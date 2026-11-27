# Maximum-weight independent set over a tree decomposition

Given a graph $G$ with vertex weights $w : V \to \mathbb{N}$ and a rooted tree decomposition with $N$ nodes and bags of size at most $k + 1$, the dynamic program over subsets of bags (child-to-parent projection of tables indexed by bitmasks, with independence checked inside bags) computes the maximum total weight of an independent set of $G$; for unit weights it computes the independence number. On the word RAM it runs in $O\big(N \cdot 2^{k+1} \cdot (k+1)^2\big)$ instructions plus input reading, at word sizes holding $N (k+1) \max w$.

## Proof sketch

For each node and each independent subset $S$ of its bag, store the best weight of an independent set of the subgraph below whose trace on the bag is $S$; children are combined by restricting to the parent bag and adding the weight of forgotten vertices.

## Depends on

- [Tree-decomposition](../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- M. Cygan, F. V. Fomin, L. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk and S. Saurabh, "Parameterized Algorithms", Springer, 2015.
- T. Kloks, "Treewidth: Computations and Approximations", LNCS 842, Springer, 1994.
