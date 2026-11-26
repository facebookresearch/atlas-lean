# Turán density of a general graph (Erdős–Stone–Simonovits)

Let $H$ be a graph on a finite vertex set with chromatic number $\chi(H) = r + 1$, where $r \ge 1$ (equivalently, $H$ has at least one edge). Then its Turán density is

$$\pi(H) = \lim_{n \to \infty} \frac{\mathrm{ex}(n, H)}{\binom{n}{2}} = 1 - \frac{1}{r} = \frac{\chi(H) - 2}{\chi(H) - 1}.$$

Lower bound: the Turán graph $T(n, r)$ is $r$-colourable and so contains no copy of $H$. Upper bound: an $(r+1)$-colouring places $H$ inside $K_{r+1}(t)$ with $t = \lvert V(H)\rvert$. Containment can only raise extremal numbers, and $\pi(K_{r+1}(t)) \le 1 - 1/r$ by the Erdős–Stone theorem.

For bipartite $H$ ($r = 1$) the formula gives $\pi(H) = 0$, that is, $\mathrm{ex}(n, H) = o(n^2)$.

## Informally uses

- [Turán density of complete multipartite graphs](turan-density-complete-equipartite-graph.md): the upper bound.
- [Lower bound on the Turán density, chromatic form](one-sub-inv-le-turan-density-of-chromati.md): the lower bound.

## Sources

- J. Noel, *Extremal Combinatorics* lecture notes (version of 15 Nov 2026), extremalcombinatorics.com, Example 3.3.1 and Theorem 3.3.10. There the formula is stated as $\pi(H) = (\chi(H) - 2)/(\chi(H) - 1)$ for every graph with at least one edge and attributed to Erdős and Stone.
