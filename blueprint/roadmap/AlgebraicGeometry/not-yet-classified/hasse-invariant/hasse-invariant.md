# Hasse coefficient of a Weierstrass curve

For a Weierstrass curve $W$ over a commutative
ring $R$ and $q \in \mathbb{N}$, `W.hasseInvariant q` is the coefficient of $X^{q-1}$ in
$\Psi(X)^{(q-1)/2}$, where $\Psi(X) = 4X^3 + b_2X^2 + 2b_4X + b_6$ is `W.twoTorsionPolynomial`,
so that $W$ is the curve $(2y + a_1x + a_3)^2 = \Psi(x)$; subtraction and division in
$\mathbb{N}$ are truncated.

When $R$ is a field whose characteristic is an odd prime $p$ and $q = p$, this is the coefficient
in the Hasse criterion (Silverman, *The Arithmetic of Elliptic Curves*, Theorem V.4.1(a)) for the
model $Y^2 = \Psi(x)$ of $W$, that is, the Hasse invariant of $W$. For other $q$ it is only a
coefficient: for example `W.hasseInvariant 2 = 0` for every $W$, because $(2 - 1)/2 = 0$.
