# The integrality gap of the subtour LP for metric TSP is below 3/2

There is an absolute constant $\epsilon > 10^{-36}$ such that for every metric TSP instance the max-entropy rounding algorithm, run with approximate marginals $\mathbb{P}_{\mu_\lambda}[e \in T] \le (1+\delta)x_e$ for a suitable $\delta$, returns in polynomial time a Hamiltonian cycle $H$ with $\mathbb{E}[c(H)] \le (\tfrac32-\epsilon)\,\mathrm{OPT}_{\mathrm{LP}}$. Consequently

$$
\sup\Big\{\frac{\mathrm{OPT}}{\mathrm{OPT}_{\mathrm{LP}}} : (V,c)\ \text{metric},\ \mathrm{OPT}_{\mathrm{LP}} > 0\Big\} \le \frac32-10^{-36}.
$$

The ratio is taken over instances with positive LP optimum: all-zero costs are allowed, and for them both optima vanish while the inequality $\mathbb{E}[c(H)] \le (\tfrac32-\epsilon)\mathrm{OPT}_{\mathrm{LP}}$ still holds.

while instance families with ratio tending to $\tfrac43$ show that this integrality gap is at least $\tfrac43$.

## Proof sketch

The later paper keeps the structure of the approximation analysis but replaces its cut analysis (Section 4 of the 2021 paper) by one that refers only to near minimum cuts of $x$, never to an optimal tour: it builds slacks with $s_e \ge -\beta x_e$, $s^* \ge 0$ and, for every $\eta$-near minimum cut $S$ of $x$ that is odd in the sampled tree, $s(\delta(S))+s^*(\delta(S)) \ge 0$, with $\mathbb{E}[s^*_e] \le 125\eta\beta x_e$ and $\mathbb{E}[s_e] \le -\tfrac13\epsilon_P\beta x_e$ for the exact max-entropy distribution $\mu$ with marginals $x$. Then $y=x/2+s+s^*$ lies in the $O$-join dominant and $\mathbb{E}_\mu[c(y)] \le (\tfrac12-\tfrac16\epsilon_P\beta)c(x)$. The sampler only has approximate marginals, so the analysis transfers to $\mu_\lambda$: stability of maximum entropy distributions gives $\|\mu-\mu_\lambda\|_1 = O(n^4\delta)$, the correction for every tree costs at most $c(x)/2$ by Wolsey's bound, and the tree costs $\mathbb{E}_{\mu_\lambda}[c(T)] \le (1+\delta)c(x)$; choosing $\delta \ll n^{-4}$ makes these errors smaller than the gain.

## Depends on

- [Subtour elimination LP of a metric TSP instance](subtour-elimination-lp.md)
- [Max-entropy rounding algorithm for metric TSP](max-entropy-tsp-algorithm.md)
- [Integrality gaps of linear programming relaxations](../../lp-based-approximation/integrality-gaps-of-linear-programming.md)

## Proof depends on

- [Karlin-Klein-Oveis Gharan: max-entropy rounding beats 3/2 for metric TSP](kko-three-halves-minus-epsilon.md)
- [Wolsey's bound: tree plus minimum T-join costs at most 3/2 of the subtour LP](wolsey-three-halves-subtour.md)
- [Max-entropy spanning tree distributions are lambda-uniform and approximately computable](max-entropy-lambda-uniform-computable.md)
- [Near-minimum cuts, atoms and polygon representations of a Held-Karp point](near-min-cuts-polygon.md)
- [Polygons of near-minimum cuts crossed on one side (Karlin-Klein-Oveis Gharan)](one-sided-polygon-structure.md)
- [T-joins and the T-join dominant polyhedron](t-join-dominant.md)

## Sources

- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Bound on the Integrality Gap of the Subtour LP for TSP", FOCS (2022), arXiv:2105.10043, Theorem 1.1, Theorem 6.1 and Section 6.2.
- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409, Fact 2.2 and Algorithm 1.
