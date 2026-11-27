# Karlin-Klein-Oveis Gharan: max-entropy rounding beats 3/2 for metric TSP

There is an absolute constant $\epsilon > 10^{-36}$ such that for every metric TSP instance $(V,c)$ the max-entropy rounding algorithm runs in randomized polynomial time and outputs a Hamiltonian cycle $H$ with

$$
\mathbb{E}[c(H)] \le \Big(\frac32-\epsilon\Big)\,\mathrm{OPT}.
$$

Thus metric TSP has a randomized $(\tfrac32-10^{-36})$-approximation algorithm in expectation, the first improvement over the Christofides-Serdyukov factor $\tfrac32$. Combined with the reduction of Traub, Vygen and Zenklusen, metric path TSP also admits a randomized $(\tfrac32-\epsilon')$-approximation for some absolute $\epsilon' > 0$.

## Proof sketch

By the Edmonds–Johnson theorem the parity correction costs at most $c(y)$ for every point $y$ of the $O$-join dominant, where $O$ is the set of odd-degree vertices of the sampled tree $T$. Let $x^*$ be the incidence vector of an optimal tour and $z=(x+x^*)/2$. The proof builds random slack vectors $s$ on LP edges and $s^* \ge 0$ on tour edges and takes $y=x/4+s$ on LP edges plus $x^*/4+s^*$ on tour edges, so that $y(\delta(S)) = z(\delta(S))/2 + s(\delta(S)) + s^*(\delta(S))$. A cut needs payment only when it is odd for the correction set, that is, when $|\delta(S) \cap T|$ is odd: for every $\eta$-near minimum cut $S$ of $z$ with $|\delta(S) \cap T|$ odd the slacks satisfy $s(\delta(S))+s^*(\delta(S)) \ge 0$, while $s_e \ge -\beta x_e$ with $\beta=\eta/4.1$ keeps all other cuts satisfied. Near minimum cuts are organized into a laminar hierarchy of degree cuts and polygon cuts using the one-sided polygon structure, and for the strongly Rayleigh measure $\mu_\lambda$ good edges have their relevant cuts simultaneously even with constant probability by the joint count bound and negative dependence. This gives $\mathbb{E}[s_e] \le -\tfrac13\epsilon_P\beta x_e$ and $\mathbb{E}[s^*_{e^*}] \le 218\eta\beta$, hence $\mathbb{E}[c(y)] \le \mathrm{OPT}/4 + c(x)/4 + 218\eta\beta\,\mathrm{OPT} - \tfrac13\epsilon_P\beta\,c(x) \le (\tfrac12-\tfrac16\epsilon_P\beta)\mathrm{OPT}$ for a suitable $\eta$, using $c(x) \le \mathrm{OPT}$. The tree costs $c(x)$ in expectation up to the error from approximate marginals. Charging only the LP point $x$, rather than both $x/4$ and $x^*/4$, is the different argument of the integrality-gap result.

## Depends on

- [Max-entropy rounding algorithm for metric TSP](max-entropy-tsp-algorithm.md)
- [Approximation algorithms and approximation ratios](../approximation-algorithms-and-approximation-ratios.md)

## Proof depends on

- [Wolsey's bound: tree plus minimum T-join costs at most 3/2 of the subtour LP](wolsey-three-halves-subtour.md)
- [Lambda-uniform spanning tree measures are strongly Rayleigh](lambda-uniform-trees-strongly-rayleigh.md)
- [Negative dependence and Poisson-binomial counts under strongly Rayleigh measures](strongly-rayleigh-negative-dependence.md)
- [Joint count probabilities for strongly Rayleigh measures (Karlin-Klein-Oveis Gharan)](sr-joint-count-bound.md)
- [Polygons of near-minimum cuts crossed on one side (Karlin-Klein-Oveis Gharan)](one-sided-polygon-structure.md)
- [T-joins and the T-join dominant polyhedron](t-join-dominant.md)
- [Edmonds-Johnson theorem: a minimum T-join costs the minimum of the T-join dominant](edmonds-johnson-t-join-dominant.md)
- [Near-minimum cuts, atoms and polygon representations of a Held-Karp point](near-min-cuts-polygon.md)
- [Strongly Rayleigh probability measures on subsets of a ground set](strongly-rayleigh-measure.md)

## Sources

- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409, Theorems 1.1, 1.2 and 3.1 and the proof of Theorem 1.1 in Section 3.
