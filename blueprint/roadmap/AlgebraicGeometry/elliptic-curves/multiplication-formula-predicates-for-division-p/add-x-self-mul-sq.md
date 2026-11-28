# Doubling formula

Let $W$ be a Weierstrass curve over a field $F$. If $x_1, y_1 \in F$
satisfy the Weierstrass equation of $W$ and $y_1 \ne \operatorname{negY}(x_1, y_1)$, then the
$x$-coordinate `addX x₁ x₁ (slope x₁ x₁ y₁ y₁)` of $(x_1, y_1) + (x_1, y_1)$, multiplied by
$\Psi_2^2(x_1)$, is $\Phi_2(x_1)$, where $\Psi_2^2$ and $\Phi_2$ are the polynomials `W.Ψ₂Sq` and
`W.Φ 2`. This is Mathlib's `Affine.addX_self_of_Y_ne` with the denominator cleared.
