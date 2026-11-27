# Metric TSP with a half-integral subtour LP optimum is 1.49993-approximable

There is a randomized polynomial-time algorithm that, given a metric TSP instance $(V,c)$ and any feasible solution $x$ of its subtour elimination LP with $x_e \in \{0,\tfrac12,1\}$ for every edge $e$, outputs a tour of expected cost at most $1.49993\cdot c^{\top}x$. As a corollary, on every instance whose subtour LP has a half-integral optimal solution (a half-integral instance) the expected tour cost is at most $1.49993\cdot\mathrm{OPT}_{\mathrm{LP}} \le 1.49993\cdot\mathrm{OPT}$. Half-integral instances are conjectured (Schalekamp, Williamson and van Zuylen) to attain the integrality gap of the subtour LP, in which case this gap would be at most $1.49993$.

## Proof sketch

Assume, splitting a vertex if necessary, that there is an edge $e^+$ with $x_{e^+}=1$ and $c(e^+)=0$. The algorithm (Section 2.4) samples a spanning tree $T^-$ from the $\lambda$-uniform distribution with marginals $z$, where $z_{e^+}=0$ and $z_e=x_e$ otherwise, forms the 1-tree $T=T^- + e^+$, and adds a minimum-cost $O$-join for the set $O$ of odd-degree vertices of $T$; this corrects the parity of the 1-tree, not of a spanning tree. The tree costs $c^{\top}x$ in expectation up to an error of $2^{-n}$. On the half-integral support the minimum cuts of value 2 form a cactus-like laminar hierarchy of degree cuts and cycle cuts, along which the distribution decomposes into independent pieces. A constant fraction of the edges are good, meaning that the relevant cuts are even with constant probability by negative dependence of the strongly Rayleigh measure; reducing the trivial correction $x/2$ on good edges while paying on cuts that are odd in $T$ lowers the expected correction cost below $\tfrac12 c^{\top}x$ by a fixed fraction.

## Depends on

- [Subtour elimination LP of a metric TSP instance](subtour-elimination-lp.md)
- [Approximation algorithms and approximation ratios](../../approximation-algorithms-and-approximation-ratios.md)
- [Integrality gaps of linear programming relaxations](../../lp-based-approximation/integrality-gaps-of-linear-programming.md)

## Proof depends on

- [Max-entropy rounding algorithm for metric TSP](max-entropy-tsp-algorithm.md)
- [Negative dependence and Poisson-binomial counts under strongly Rayleigh measures](strongly-rayleigh-negative-dependence.md)

## Sources

- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "An Improved Approximation Algorithm for TSP in the Half Integral Case", STOC (2020), arXiv:1908.00227, Theorem 1.2 and Section 2.4 (Algorithm 1).
