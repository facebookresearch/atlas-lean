# Russo's formula, covariance form, for an arbitrary event

Let $E$ be a finite set and $A \subseteq \{0,1\}^E$ an arbitrary event. For every real $p \notin \{0, 1\}$, the [Bernoulli weight](prob.md) $p \mapsto P_p(A)$ is differentiable at $p$ with

$$\frac{d}{dp} P_p(A) = \frac{1}{p(1-p)} \sum_{e \in E} \big(P_p(A \cap \{\omega_e = 1\}) - P_p(\omega_e = 1)\,P_p(A)\big).$$

Unlike [Russo's formula](has-deriv-at-prob-eq-sum-pivotal-prob.md) in its pivotal form, $A$ need not be increasing.

## Background

- [Russo's formula](deriv-prob-eq-sum-pivotal-prob.md): the pivotal form for increasing events (Proposition 2.7 of the lecture notes); for an increasing event the covariance with $\omega_e$ equals $p(1 - p)$ times the probability that $e$ is pivotal.
- [Russo's formula, covariance form for increasing events](../../../percolation/phase-transition/sharp-thresholds-from-influences/russo-formula.md): the special case this result generalises.
- [Influence of a coordinate on the Boolean cube](../../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md): the influences of Boolean-function analysis at $p = 1/2$; for a monotone function the covariance term of coordinate $e$ is, up to normalisation, its influence.
- [Covariance under a product weight](../../../../Combinatorics/boolean-functions/osss-inequality-for-decision-trees/cov.md): the covariance used by the OSSS inequality, the other route to sharpness.

## Sources

- H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS (version of 7 October 2018), Proposition 2.6 and equation (2.2).
- G. A. Margulis, *Probabilistic characteristics of graphs with large connectivity*, Problemy Peredači Informacii 10 (1974), 101–108.
- L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981), 229–237.
