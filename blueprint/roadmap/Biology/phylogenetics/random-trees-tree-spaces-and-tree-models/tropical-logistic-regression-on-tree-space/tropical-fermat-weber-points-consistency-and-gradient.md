# Tropical Fermat–Weber points of tree samples: consistency and gradient

For points $X_1, \dots, X_n$ in the tropical projective torus $\mathbb{R}^e/\mathbb{R}\mathbf{1}$ (for example, ultrametric gene trees), a **tropical Fermat–Weber point** is any minimiser of

$$f(\omega) = \sum_{i=1}^n d_{\mathrm{tr}}(X_i, \omega), \qquad d_{\mathrm{tr}}(v, w) = \max_j (v_j - w_j) - \min_j (v_j - w_j).$$

**Proposition (consistency).** Let $X_1, X_2, \dots$ be i.i.d. with a density $g$ that is symmetric about a centre $\omega^*$, i.e. $g(\omega^* + \delta) = g(\omega^* - \delta)$ for all $\delta$, positive on a neighbourhood of $\omega^*$, and such that $E\, d_{\mathrm{tr}}(X_1, \omega^*) < \infty$. Then every choice of Fermat–Weber points $\tilde\omega_n$ of $X_1, \dots, X_n$ satisfies $\tilde\omega_n \to \omega^*$ in probability; in particular the diameter of the Fermat–Weber set tends to $0$ in probability. If moreover the $\tilde\omega_n$ are chosen in the space of ultrametric trees and $\omega^*$ lies in the interior of a maximal cone of that space (a binary tree at positive distance from every boundary between topologies), then the probability that $\tilde\omega_n$ has the tree topology of $\omega^*$ tends to $1$.

**Proposition (gradient).**
1. $f$ is differentiable at $\omega$ if and only if each vector $\omega - X_i$ has a unique maximal and a unique minimal coordinate; then

$$\big(\nabla f(\omega)\big)_j = \#\{i : \operatorname{argmax}_\ell (\omega - X_i)_\ell = j\} - \#\{i : \operatorname{argmin}_\ell (\omega - X_i)_\ell = j\},$$

an integer vector.
2. If the gradient exists and equals $0$, then $\omega$ is a Fermat–Weber point.

## Depends on

- [Tropical Laplace distribution on the tropical projective torus](tropical-laplace-distribution-on-the-tropical-projective-torus.md)

## Expansion

For consistency, the expected objective $E\,d_{\mathrm{tr}}(X, \omega)$ is uniquely minimised at $\omega^*$: with $F(x) = d_{\mathrm{tr}}(x, \omega) + d_{\mathrm{tr}}(2\omega^* - x, \omega) - 2 d_{\mathrm{tr}}(x, \omega^*) \ge 0$ (triangle inequality) and $F > 0$ near $\omega^*$ for $\omega \ne \omega^*$, symmetry gives $E\,d_{\mathrm{tr}}(X, \omega) \ge E\,d_{\mathrm{tr}}(X, \omega^*)$, strictly because $g$ is positive where $F$ is, and integrability makes these expectations finite; an argmin-consistency theorem finishes. Symmetry alone is not enough: in $\mathbb R^2/\mathbb R\mathbf 1$, equal uniform mass on $[-2,-1]$ and $[1,2]$ in the difference coordinate is symmetric about $0$, yet for odd $n$ every sample median is at distance at least $1$ from $0$. The topology statement follows because a neighbourhood of an interior point of a maximal cone contains only trees of that topology. For the gradient, perturbing one coordinate of $\omega$ changes $d_{\mathrm{tr}}(X_i, \omega)$ linearly by $+1$, $-1$ or $0$ depending on whether that coordinate is the unique argmax or argmin of $\omega - X_i$; ties break differentiability. Since $f$ is convex, a zero gradient certifies a global minimiser, which makes gradient descent a cheap alternative to the linear-programming computation of Fermat–Weber points.

## Sources

- G. Aliatimis, R. Yoshida, B. Boyacı, J. A. Grant, *Tropical logistic regression model on space of phylogenetic trees*, Bull. Math. Biol. 86 (2024), 99 (Eq. (15), Propositions 7–8, Lemmas 1–2 and proofs in the appendix). <https://doi.org/10.1007/s11538-024-01327-8> (PMCID: PMC11219468)
