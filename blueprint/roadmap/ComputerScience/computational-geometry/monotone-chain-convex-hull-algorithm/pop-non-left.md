# Pop step of the monotone-chain scan

Let $\Bbbk$ be a linearly ordered field, let
$p \in \Bbbk^2$, and write $u \times v = u_1 v_2 - v_1 u_2$ for the cross product. Given a
stack of points of $\Bbbk^2$ listed top first, while the stack has at least two points, with
top $a$ and next point $b$, and $(a - b) \times (p - b) \le 0$ (so $b \to a \to p$ is not a
strict left turn), remove $a$. The result is the first stack reached that has fewer than two
points or whose top two points $a, b$ satisfy $(a - b) \times (p - b) > 0$; that stack is
returned unchanged. Each test of the sign of $(a - b) \times (p - b)$ costs one unit, and
nothing else is charged.
