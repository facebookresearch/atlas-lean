# Dadush-Huiberts shadow bound for smoothed unit linear programs

Let $W \subseteq \mathbb{R}^d$ be a fixed two-dimensional subspace, let $n \ge d \ge 3$ and $\sigma > 0$, and let $a_1, \dots, a_n \in \mathbb{R}^d$ be independent Gaussian vectors with variance $\sigma^2$ and centers of norm at most $1$. Then

$$
\mathbb{E}\,\big|\mathrm{edges}(\mathrm{conv}(a_1, \dots, a_n) \cap W)\big| = O\!\left(d^2 \sqrt{\log n}\, \sigma^{-2} + d^{2.5} \log n \, \sigma^{-1} + d^{2.5} \log^{3/2} n\right) ,
$$

so both the polar-section shadow size $S_{\mathrm{e}}(n, d, \sigma)$ and the shadow bound $S(n, d, \sigma)$ satisfy this bound.

Consequently a two-phase shadow vertex method (the symmetric random vertex algorithm) solves smoothed programs with an expected

$$
O\!\left(d^2 \sqrt{\log n}\, \sigma^{-2} + d^3 \log^{3/2} n\right)
$$

pivots. In the purely Gaussian model ($\bar A = 0$), Borgwardt's bound $\Theta(d^{3/2} \sqrt{\log n})$ as $n \to \infty$ shows that the shadow size is $\Omega(d^{3/2}\sqrt{\log n})$ in the smoothed model for $n$ large enough compared to $d$.

## Proof sketch

By the polar section lemma it suffices to count edges of the random polygon $Q \cap W$. Following the Kelner-Spielman edge-counting strategy, the expected number of edges is bounded by the expected perimeter of $Q \cap W$, which is at most $2\pi\,\mathbb{E}\max_i \|\pi_W(a_i)\| = O(1 + \sigma\sqrt{\log n})$ by Gaussian tail bounds for the two-dimensional projections, divided by a lower bound on the expected length of an edge, which is established by conditioning on the hyperplane through the defining rows and using that Gaussian densities are smooth (log-Lipschitz on the relevant scale) and have light tails. The analysis is modular and also covers Laplace perturbations.

## Depends on

- [Gaussian-smoothed linear programs and smoothed pivot complexity](gaussian-smoothed-linear-programs.md)
- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)

## Proof depends on

- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)
- [Largest singular value of a standard Gaussian matrix](../../../Probability/high-dimensional-probability/measure-real-sigma-max-ge-le.md)

## Sources

- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667, Theorems 13, 14, 22 and 47, Table 1.
- A. Deshpande, D. A. Spielman, "Improved Smoothed Analysis of the Shadow Vertex Simplex Method", FOCS (2005).
- K. H. Borgwardt, "The Simplex Method: A Probabilistic Analysis", Springer (1987).
