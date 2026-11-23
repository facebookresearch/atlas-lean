# Sinclair's Poincaré hypothesis is a lower bound on the spectral gap

Let $S$ be a finite set, $\pi$ a probability vector on $S$ ($\pi \ge 0$, $\sum_x \pi(x) = 1$), $P$ a real $S \times S$ matrix
with nonnegative entries and rows summing to $1$, and $B > 0$. Suppose some function has nonzero
[variance](weighted-variance.md) $\operatorname{Var}_\pi$. Then $1/B \le \lambda(P, \pi)$, where
$\lambda$ is the [spectral gap](spectral-gap.md), if and only if for every
$\psi : S \to \mathbb{R}$

$$\sum_{x, y} \bigl(\psi(x) - \psi(y)\bigr)^2 \pi(x)\pi(y) \le B \sum_{x, y} \bigl(\psi(x) - \psi(y)\bigr)^2 \pi(x) P(x, y) .$$

This Poincaré inequality is the hypothesis of Sinclair's spectral-gap and mixing bounds ([a
Poincaré inequality bounds the spectral
gap](../canonical-paths-and-multicommodity-flow/one-le-mul-one-sub-of-poincare.md), [a Poincaré
inequality bounds the mixing time of the lazy
chain](../mixing-times-of-markov-chains/is-mixed-at-of-poincare.md)).

## Sources

- P. Diaconis and L. Saloff-Coste, *Logarithmic Sobolev inequalities for finite Markov chains*, Annals of Applied Probability 6 (1996), 695–750, equation (1.4).
- A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*, Combinatorics, Probability and Computing 1 (1992), 351–370.
