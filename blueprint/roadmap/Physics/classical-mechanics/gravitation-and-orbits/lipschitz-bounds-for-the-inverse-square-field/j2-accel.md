# J2 perturbing acceleration of an axially symmetric body

For real numbers $\mu$ (gravitational parameter), $R$ (reference radius) and $J_2$ (oblateness
coefficient, of either sign), and a position $r = (x, y, z)$ in three-dimensional Euclidean space,
let $u = z^2/\|r\|^2$. The $J_2$ perturbing acceleration is

$$a(r) = -\frac{3 J_2 \mu R^2}{2\|r\|^5}\Bigl((1 - 5u)\,r + 2\,(0, 0, z)\Bigr),$$

with components $(1 - 5u)x$, $(1 - 5u)y$ and $(3 - 5u)z$ times the scalar factor. It is meant for
$r \ne 0$; at $r = 0$ its value is $0$, since with the convention $x/0 = 0$ the scalar factor and
$u$ are $0$. Away from the origin it is the gradient of the geopotential term
$-(\mu/\|r\|)\,J_2\,(R/\|r\|)^2\,P_2(z/\|r\|)$, with $P_2(t) = (3t^2 - 1)/2$, in the geodesy sign
convention where the acceleration is the gradient of the potential; positive $J_2$ describes a body
flattened along the $z$-axis, such as the Earth ($J_2 \approx 1.083 \times 10^{-3}$). In the
physical reading $\mu > 0$ and $R > 0$; the definition takes any real $\mu$, $R$ and $J_2$.
