# Multiplication-formula predicate

Let $P = (x, y)$ be a nonsingular affine point of a
Weierstrass curve $W$ over a field and let $m \in \mathbb{N}$, and let $\Phi_m$ and $\Psi_m^2$ be
the polynomials `W.Φ m` and `W.ΨSq m`. The predicate says that $\Psi_m^2(x) \ne 0$ and
$\operatorname{xCoordOrZero}(m \cdot P) \cdot \Psi_m^2(x) = \Phi_m(x)$, where `Point.xCoordOrZero`
is the $x$-coordinate of an affine point and $0$ at the point at infinity. It does not separately
require $m \cdot P$ to be affine: if $m \cdot P$ is the point at infinity, the equation says
$\Phi_m(x) = 0$.
