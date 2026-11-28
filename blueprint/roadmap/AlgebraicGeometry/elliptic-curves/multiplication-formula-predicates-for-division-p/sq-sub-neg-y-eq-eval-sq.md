# Duplication denominator as a square

Let $W$ be a Weierstrass curve over a field $F$. If
$x, y \in F$ satisfy the Weierstrass equation of $W$, then
$(y - \operatorname{negY}(x, y))^2 = \Psi_2^2(x)$, where
$\operatorname{negY}(x, y) = -y - a_1x - a_3$ is the $y$-coordinate of the negative of $(x, y)$ and
$\Psi_2^2$ is the polynomial `W.Ψ₂Sq`. This is Mathlib's `Affine.den_duplication_eq`, stated with
`Ψ₂Sq` and `negY`.
