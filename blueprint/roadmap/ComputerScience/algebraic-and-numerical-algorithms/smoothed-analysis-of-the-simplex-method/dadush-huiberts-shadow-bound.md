# Dadush-Huiberts shadow bound for smoothed unit linear programs

For $d \ge 3$, $n \ge d$ and $\sigma > 0$,

$$
S(n, d, \sigma) = O\!\left(d^2 \sqrt{\log n}\, \sigma^{-2} + d^{2.5} \log^{3/2} n \, (1 + \sigma^{-1})\right) .
$$

Consequently a two-phase shadow vertex method (the symmetric random vertex algorithm) solves smoothed programs with an expected

$$
O\!\left(d^2 \sqrt{\log n}\, \sigma^{-2} + d^3 \log^{3/2} n\right)
$$

pivots. In the purely Gaussian model with $n \to \infty$, Borgwardt's lower bound $\Omega(d^{3/2} \sqrt{\log n})$ on the shadow size also applies in the smoothed model for $n$ large enough.

## Proof sketch

By the polar section lemma it suffices to count edges of the random polygon $Q \cap W$. Following the Kelner-Spielman edge-counting strategy, the expected number of edges is bounded by the expected perimeter of $Q \cap W$, which is $O(1 + \sigma\sqrt{d \log n})$ by Gaussian norm bounds, divided by a lower bound on the expected length of an edge, which is established by conditioning on the hyperplane through the defining rows and using that Gaussian densities are smooth (log-Lipschitz on the relevant scale) and have light tails. The analysis is modular and also covers Laplace perturbations.

## Depends on

- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)
- [The shadow vertex pivot rule and the smoothed shadow bound](shadow-vertex-rule-and-shadow-bound.md)
- [Largest singular value of a standard Gaussian matrix](../../../Probability/high-dimensional-probability/measure-real-sigma-max-ge-le.md)

## Proof depends on

- [Shadow vertices are bounded by edges of the polar section](shadow-vertices-and-polar-section.md)
- [Largest singular value of a standard Gaussian matrix](../../../Probability/high-dimensional-probability/measure-real-sigma-max-ge-le.md)

## Sources

- D. Dadush, S. Huiberts, "A Friendly Smoothed Analysis of the Simplex Method", SIAM Journal on Computing 49 (2020), STOC (2018), arXiv:1711.05667.
- A. Deshpande, D. A. Spielman, "Improved Smoothed Analysis of the Shadow Vertex Simplex Method", FOCS (2005).
- K. H. Borgwardt, "The Simplex Method: A Probabilistic Analysis", Springer (1987).
