# Perfect graphs are those with STAB = QSTAB

A finite graph $G$ is [perfect](../../graph-coloring/part-01/perfect-graphs/is-perfect.md) if and only if $\mathrm{STAB}(G) = \mathrm{QSTAB}(G)$. Knuth proves "perfect implies equal" by duplicating vertices (his Theorem 31) and the converse with antiblocking polyhedra (his Corollary 30 and Theorem 32). Since $\mathrm{STAB}(G) \subseteq \mathrm{TH}(G) \subseteq \mathrm{QSTAB}(G)$, for perfect graphs all three coincide, which is how Grötschel, Lovász and Schrijver optimise over the stable set polytope of a perfect graph in polynomial time.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, Theorems 31 and 32.
