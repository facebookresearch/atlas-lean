# Tropical Fermat–Weber points of tree samples: consistency and gradient

For points $X_1, \dots, X_n$ in the tropical projective torus $\mathbb{R}^e/\mathbb{R}\mathbf{1}$ (for example, ultrametric gene trees), a **tropical Fermat–Weber point** is any minimiser of
$$f(\omega) = \sum_{i=1}^n d_{\mathrm{tr}}(X_i, \omega), \qquad d_{\mathrm{tr}}(v, w) = \max_j (v_j - w_j) - \min_j (v_j - w_j).$$

**Proposition (consistency).** If $X_1, X_2, \dots$ are i.i.d. from a density symmetric about a centre $\omega^*$, i.e. $f(\omega^* + \delta) = f(\omega^* - \delta)$ for all $\delta$, then every choice of Fermat–Weber points $\tilde\omega_n$ satisfies $\tilde\omega_n \to \omega^*$ in probability. In particular the Fermat–Weber set shrinks to a single point and its tree topology is eventually fixed.

**Proposition (gradient).**
1. $f$ is differentiable at $\omega$ if and only if each vector $\omega - X_i$ has a unique maximal and a unique minimal coordinate; then
$$\big(\nabla f(\omega)\big)_j = \#\{i : \operatorname{argmax}_\ell (\omega - X_i)_\ell = j\} - \#\{i : \operatorname{argmin}_\ell (\omega - X_i)_\ell = j\},$$
an integer vector.
2. If the gradient exists and equals $0$, then $\omega$ is a Fermat–Weber point.

## Depends on

- [Tropical Laplace distribution on the space of ultrametric trees](tropical-laplace-distribution-on-the-tropical-projective-torus.md)

## Expansion

For consistency, the expected objective $E\,d_{\mathrm{tr}}(X, \omega)$ is uniquely minimised at $\omega^*$: with $F(x) = d_{\mathrm{tr}}(x, \omega) + d_{\mathrm{tr}}(2\omega^* - x, \omega) - 2 d_{\mathrm{tr}}(x, \omega^*) \ge 0$ (triangle inequality) and $F > 0$ near $\omega^*$ for $\omega \ne \omega^*$, symmetry gives $E\,d_{\mathrm{tr}}(X, \omega) > E\,d_{\mathrm{tr}}(X, \omega^*)$, and an argmin-consistency theorem finishes. For the gradient, perturbing one coordinate of $\omega$ changes $d_{\mathrm{tr}}(X_i, \omega)$ linearly by $+1$, $-1$ or $0$ depending on whether that coordinate is the unique argmax or argmin of $\omega - X_i$; ties break differentiability. Since $f$ is convex, a zero gradient certifies a global minimiser, which makes gradient descent a cheap alternative to the linear-programming computation of Fermat–Weber points.

## Sources

- G. Aliatimis, R. Yoshida, B. Boyacı, J. A. Grant, *Tropical logistic regression model on space of phylogenetic trees*, Bull. Math. Biol. 86 (2024), 99 (Eq. (15), Propositions 7–8, Lemmas 1–2 and proofs in the appendix). <https://doi.org/10.1007/s11538-024-01327-8> (PMCID: PMC11219468)
