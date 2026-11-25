# Rescaling the fixed-fixed problem to the unit interval

Let $L > 0$, $k \ne 0$ and $f, u \colon \mathbb{R} \to \mathbb{R}$. Then $u$ solves the
[fixed-fixed problem](is-fixed-fixed-solution.md) on $[0, L]$ with rigidity $k$ and load $f$ if and
only if $v(\xi) = u(L \xi)$ solves the fixed-fixed problem on $[0, 1]$ with rigidity $1$ and load
$g(\xi) = \frac{L^2}{k} f(L\xi)$:

$$-v''(\xi) = \frac{L^2}{k}\, f(L\xi) \quad (\xi \in [0, 1]), \qquad v(0) = v(1) = 0,$$

with the second derivatives taken within $[0, L]$ and $[0, 1]$. The change of variables is
$x = L \xi$.
