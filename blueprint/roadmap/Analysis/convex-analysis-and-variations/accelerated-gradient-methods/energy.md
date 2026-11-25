# Energy of the Euclidean Bregman-Lagrangian flow

For curves $X, Z : \mathbb{R} \to E$ in a real Hilbert space, a function $f : E \to \mathbb{R}$, a time scale $\beta : \mathbb{R} \to \mathbb{R}$ and a point $x^\star \in E$,

$$
\mathcal E_t = \tfrac12\|Z_t - x^\star\|^2 + e^{\beta_t}\,\bigl(f(X_t) - f(x^\star)\bigr).
$$

This is the energy (2.8) of Wibisono, Wilson and Jordan, $D_h(x^\star, X_t + e^{-\alpha_t}\dot X_t) + e^{\beta_t}(f(X_t) - f(x^\star))$, for the Euclidean distance-generating function $h = \|\cdot\|^2/2$, writing $Z = X + e^{-\alpha}\dot X$.

## Background

- [Bregman divergence](../mirror-descent/bregman.md): $D_h(x, y) = h(x) - h(y) - \langle \nabla h(y), x - y\rangle$, equal to $\|x - y\|^2/2$ here.

## Sources

- A. Wibisono, A. C. Wilson and M. I. Jordan, *A variational perspective on accelerated methods in optimization*, arXiv:1603.04245v1 (PNAS 113 (2016) E7351–E7358), equation (2.8).
