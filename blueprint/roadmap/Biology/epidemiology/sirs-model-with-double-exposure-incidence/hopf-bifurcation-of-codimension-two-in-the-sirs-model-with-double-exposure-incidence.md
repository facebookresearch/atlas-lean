# Hopf bifurcation of codimension two in the SIRS model with double-exposure incidence

**Setting.** Consider the reduced SIRS model with incidence $\beta(1+\nu I)IS$ on its invariant plane, in rescaled form

$$\dot I = I(1 + pI)(A - I - R) - \frac{A}{\mathcal R_0} I, \qquad \dot R = qI - R,$$

with $p \ge 0$, $A, q > 0$, $q\mathcal R_0 < A < (q+1)\mathcal R_0$. Let $E_+ = (x, qx)$ be the larger positive equilibrium (an anti-saddle wherever it exists, with or without the backward-bifurcation saddle $E_-$). The trace of the Jacobian at $E_+$ vanishes exactly when

$$\mathcal R_0 = \mathcal R_0^H := \frac{A}{(px+1)(A - qx - x)}, \qquad A = A^H := \frac{pqx^2 + 2px^2 + x + 1}{px},$$

and then the determinant is positive iff $\operatorname{Det}(x) := qx(px+1) - 1 > 0$. Consider the two parameter regions (with $p, x > 0$, the trace-zero conditions above, and $\frac{p^2x^3 + 2px^2 + x + 1}{px} < q < \frac{p^2x^3 + 2px^2 + px + x + 1}{px}$ so that the parameter constraints hold):

$$D_1 :\ q \ge \frac{1 + px^2}{x}, \qquad D_2 :\ \frac{1}{x(px+1)} < q < \frac{1 + px^2}{x},$$

and put

$$q_H = \frac{2p^2x^3 + 2px^2 + 3px + 1}{p^2x^3 + 3px^2 + 2x + 1}.$$

**Theorem.**

1. In $D_1$, $E_+$ is a stable weak focus of order $1$ and the system undergoes a supercritical Hopf bifurcation: a stable limit cycle appears around $E_+$.
2. In $D_2$, $E_+$ is a weak focus of order at most $2$:
   - if $q > q_H$, it is a stable weak focus of order $1$ (supercritical Hopf bifurcation);
   - if $q < q_H$, it is an unstable weak focus of order $1$ (subcritical Hopf bifurcation);
   - if $q = q_H$, it is an unstable weak focus of order exactly $2$, and a Hopf bifurcation of codimension $2$ produces two limit cycles around $E_+$, the inner one stable.

Thus the model supports at most two small-amplitude limit cycles around $E_+$. In the original parameters, supercritical Hopf bifurcation means stable periodic outbreaks for almost all initial conditions when both equilibria are unstable; in the backward-bifurcation regime it gives bistability between disease extinction and an endemic equilibrium, or between extinction and a periodic outbreak.

## Depends on

- [Degenerate Bogdanov–Takens bifurcation in the SIRS model with double-exposure incidence](degenerate-bogdanov-takens-bifurcation-in-the-sirs-model-with-double-exposure-incidence.md)

## Expansion

Solving the equilibrium quadratic and the trace condition simultaneously for $\mathcal R_0$ and $A$ in terms of $(p, q, x)$ gives $\mathcal R_0^H$ and $A^H$, which parametrize the Hopf surface by the equilibrium level $x$. After moving $E_+$ to the origin, rotating to Jordan form and rescaling time by $\sqrt{\operatorname{Det}(x)}$, the successive-function method gives the first focal value

$$\sigma_1 = \frac{p\bigl[2p^2x^3 + p(2x+3)x + 1 - q\,(p^2x^3 + 3px^2 + 2x + 1)\bigr]}{2(px+1)\operatorname{Det}(x)^{3/2}} .$$

In $D_1$ the bracket is negative; in $D_2$ it vanishes exactly at $q = q_H$, where the second focal value $\sigma_2$ is positive. The map $(A, q) \mapsto (\operatorname{tr}, \sigma_1)$ has nonzero Jacobian at $(A^H, q_H)$ (its determinant is $-px(p^2x^3 + 3px^2 + 2x + 1)$), so $A$ and $q$ unfold the codimension-2 Hopf point independently; this is how two nested cycles appear. This sharpens the earlier codimension-1 Hopf analysis of the same model, which had left open whether the trace-zero equilibrium is a centre or a focus and of what order.

## Sources

- M. Lu, D. Gao, J. Huang, H. Wang, "Relative prevalence-based dispersal in an epidemic patch model", *Journal of Mathematical Biology* 86 (2023), Eqs. (2.21)–(2.27), Theorem 2.9, Remarks 2.10–2.12. <https://doi.org/10.1007/s00285-023-01887-8> (PMC9987411).
