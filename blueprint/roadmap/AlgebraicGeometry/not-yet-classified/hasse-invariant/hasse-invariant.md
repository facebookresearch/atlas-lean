# Hasse coefficient of a Weierstrass curve

For a Weierstrass curve $W$ over a commutative
ring $R$ and $q \in \mathbb{N}$, `W.hasseInvariant q` is the coefficient of $X^{q-1}$ in
$\Psi(X)^{(q-1)/2}$, where $\Psi(X) = 4X^3 + b_2X^2 + 2b_4X + b_6$ is `W.twoTorsionPolynomial`;
subtraction and division in $\mathbb{N}$ are truncated.

Over every commutative ring, $(2y + a_1x + a_3)^2 - \Psi(x)$ is $4$ times the Weierstrass
polynomial of $W$. The equation $(2y + a_1x + a_3)^2 = \Psi(x)$ is a model of $W$ only when $2$ is
invertible: then $(x, y) \mapsto (x, 2y + a_1x + a_3)$ identifies $W$ with the curve
$Y^2 = \Psi(x)$. Otherwise it can lose the curve: over $\mathbb{F}_2$, for $y^2 + y = x^3$ it
reads $1 = 1$, which $(1, 0)$ satisfies although $(1, 0)$ is not a point of the curve.

When $R$ is a field whose characteristic is an odd prime $p$, $q = p$ and $W$ is an elliptic
curve, that is, nonsingular, this is the coefficient of the Hasse criterion (Silverman, *The
Arithmetic of Elliptic Curves*, Theorem V.4.1(a)) for the model $Y^2 = \Psi(x)$ of $W$: the Hasse
invariant of $W$. For other $q$ it is only a coefficient: for example `W.hasseInvariant 2 = 0`
for every $W$, because $(2 - 1)/2 = 0$.
