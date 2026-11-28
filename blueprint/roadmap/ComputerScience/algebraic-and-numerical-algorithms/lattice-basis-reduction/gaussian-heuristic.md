# The Gaussian heuristic for lattice point counts

The Gaussian heuristic predicts that a nice region $S$ contains about $\operatorname{vol}(S)/\operatorname{vol}(L)$ points of a full-rank lattice $L\subset\mathbb{R}^n$; applied to balls it predicts a shortest nonzero vector of length $\operatorname{GH}(L)=\operatorname{vol}(L)^{1/n}V_n(1)^{-1/n}$. It is a model, not a theorem.

Let $n\ge1$, let $L\subset\mathbb{R}^n$ be a lattice of rank $n$ with covolume $\operatorname{vol}(L)>0$, and let $V_n(1)=\pi^{n/2}/\Gamma(n/2+1)$ be the volume of the Euclidean unit ball. The *Gaussian heuristic* is the prediction that, for a "nice" measurable set $S\subset\mathbb{R}^n$,

$$
\#(S\cap L)\approx \frac{\operatorname{vol}(S)}{\operatorname{vol}(L)} .
$$

Applied to balls of radius $r$, of volume $r^nV_n(1)$, it predicts

$$
\lambda_1(L)\approx \operatorname{GH}(L) := \operatorname{vol}(L)^{1/n}\,V_n(1)^{-1/n}.
$$

"Nice" is not made precise, and the prediction is not valid for every lattice or every set. A rigorous companion bound holds for every lattice of rank $n$: $\lambda_1(L)\le 2\operatorname{GH}(L)$. Chen and Nguyen use it to estimate the number of nodes of enumeration trees and, in their simulation of BKZ 2.0, the Gram–Schmidt norms of reduced blocks.

## Proof sketch

The companion bound follows from Minkowski's convex body theorem, which needs strict volume inequality: for every $r>2\operatorname{GH}(L)$ the ball of radius $r$ is convex, symmetric and has volume $r^nV_n(1)>2^n\operatorname{vol}(L)$, so it contains a nonzero lattice vector; hence $\lambda_1(L)<r$ for all such $r$, and $\lambda_1(L)\le2\operatorname{GH}(L)$. Chen and Nguyen state the bound and the heuristic, and note that in some cases the heuristic can be proved and in others refuted; it is not a theorem for general lattices and sets.

## Depends on

- [Shortest vector, independent vectors and guaranteed distance decoding problems](../../cryptography/public-key/lattice-and-code-based-cryptography/lattice-gaussians-and-smoothing-parameter/svp-sivp-givp-and-gdd.md)

## Proof depends on

- [Minkowski's convex body theorem](../../../NumberTheory/diophantine-approximation/uniform-distribution-metric/minkowski-convex-body-theorem.md)

## Sources

- Yuanmi Chen, Phong Q. Nguyen, "BKZ 2.0: Better Lattice Security Estimates", ASIACRYPT 2011, Lecture Notes in Computer Science 7073, pp. 1–20, Springer, https://doi.org/10.1007/978-3-642-25385-0_1, Section 2 (Gaussian heuristic, $\mathrm{GH}(L)$ and Minkowski's bound, p. 5), Section 3.2 Equation (1) and Section 6 (uses of the heuristic).
