# Greedy coloring along a perfect elimination order

Let $G$ be a finite simple graph with a [perfect elimination order](perfect-elimination-orders-and-chordal-graphs.md) $v_1, \dots, v_n$. Coloring $v_n, v_{n-1}, \dots, v_1$ in this order, each with the least color not used by its already colored neighbors, uses exactly $\omega(G)$ colors, the size of the largest clique. Hence $\chi(G) = \omega(G)$.

**Proof.** When $v_i$ is colored, its colored neighbors lie in $\{v_{i+1}, \dots, v_n\}$, so together with $v_i$ they form a clique and number at most $\omega(G) - 1$; the color chosen is therefore among the first $\omega(G)$. Every coloring needs at least $\omega(G)$ colors.

## Depends on

- [Perfect elimination orders and chordal graphs](perfect-elimination-orders-and-chordal-graphs.md)

## Sources

- S. Hack, D. Grund and G. Goos, "Register allocation for programs in SSA-form", *Compiler Construction (CC 2006)*, LNCS 3923, Springer, 2006, pp. 247–262, <https://compilers.cs.uni-saarland.de/papers/ssara.pdf>, Section 3: the reinsertion coloring along a perfect elimination order, whose colored neighbors form a clique, and the bound by the size of the largest clique; Hack et al. refer to M. C. Golumbic, *Algorithmic Graph Theory and Perfect Graphs*, Academic Press, 1980, for this classical fact.
