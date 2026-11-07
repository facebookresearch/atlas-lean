# Nijenhuis tensor

Let $n$ be a natural number, let $J$ assign to each point
$y \in \mathbb{R}^{2n}$ a real linear map $J(y) : \mathbb{R}^{2n} \to \mathbb{R}^{2n}$, and let
$V, W : \mathbb{R}^{2n} \to \mathbb{R}^{2n}$ be vector fields. Write $JV$ for the vector field
$y \mapsto J(y)V(y)$ and $[V, W]$ for the Lie bracket of vector fields. The Nijenhuis tensor of
$J$ at a point $x \in \mathbb{R}^{2n}$ is

$$N(V, W)(x) = [JV, JW](x) - J(x)[JV, W](x) - J(x)[V, JW](x) - [V, W](x).$$

For an almost complex structure the last term is $J^2[V, W]$, so this is the usual torsion of
$J$. When $J$ is an almost complex structure on an open set $U \subseteq \mathbb{R}^{2n}$, the
expression is $C^\infty(U)$-bilinear in $V$ and $W$ on $U$: the terms involving the derivatives
of $V$ and $W$ cancel using $J^2 = -1$, so the value at a point $x$ of $U$ depends only on
$V(x)$, $W(x)$ and the derivative of $J$ there.
