# Every symmetric submodular function has a Gomory-Hu tree

Every real-valued symmetric submodular set function $f : 2^V \to \mathbb{R}$ on a nonempty finite set $V$ has a Gomory-Hu tree (Williamson, Section 3.4, p. 86 and p. 91, with the tree edges of the form required here by Lemma 3.36). In particular, every undirected graph with nonnegative real edge weights $w$ has a Gomory-Hu tree for its cut function $X \mapsto w(\delta(X))$ (Williamson, Theorem 3.37).

## Proof sketch

Gomory and Hu's recursion: pick $s, t$ in a current super-node, take a minimum $s$-$t$ cut, and split the super-node; uncrossing shows the cut can be chosen compatible with the cuts already used, so the final tree edges are minimum cuts. Only symmetry and submodularity are used.

## Depends on

- [Gomory-Hu trees](gomory-hu-tree.md)

## Proof depends on

- [Uncrossing minimum cuts of symmetric submodular functions](uncrossing-minimum-cuts.md)

## Sources

- D. P. Williamson, "Network Flow Algorithms", Cambridge University Press, 2019, Section 3.4: p. 86, Lemma 3.36 (p. 88), Theorem 3.37 (p. 90) and the extension to symmetric submodular functions (p. 91), Exercises 3.4 and 3.5 (pp. 92-93); author-posted edition: <https://www.networkflowalgs.com/book.pdf>.
- R. E. Gomory and T. C. Hu, "Multi-Terminal Network Flows", Journal of the Society for Industrial and Applied Mathematics 9(4), 1961.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
