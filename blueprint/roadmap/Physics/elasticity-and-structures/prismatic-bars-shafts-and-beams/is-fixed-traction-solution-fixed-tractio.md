# The constructed displacement solves the fixed-traction problem

Let $L > 0$, $k \ne 0$ and $P$ real, and let $f \colon \mathbb{R} \to \mathbb{R}$ be continuous on
$[0, L]$. The [fixed-traction displacement](fixed-traction-displacement.md)

$$u(x) = \int_0^x \frac{1}{k}\left(P + \int_y^L f(z)\, dz\right) dy$$

solves the [fixed-traction problem](is-fixed-traction-solution.md): it is twice continuously
differentiable on $[0, L]$, $-k\, u''(x) = f(x)$ for every $x \in [0, L]$, $u(0) = 0$ and
$k\, u'(L) = P$, with the derivatives taken within $[0, L]$.
