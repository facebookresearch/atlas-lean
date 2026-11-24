# Displacement of a bar fixed at one end under an end force and a load

For real numbers $k$, $L$, $P$ and $x$ and a function $f \colon \mathbb{R} \to \mathbb{R}$, the
fixed-traction displacement is the primitive from the fixed end $x = 0$ of the
[load-path strain](fixed-traction-strain.md):

$$u(x) = \int_0^x \frac{1}{k}\left(P + \int_y^L f(z)\, dz\right) dy.$$

The integrals are oriented and are $0$ when the integrand is not integrable on the interval of
integration; with the convention $a/0 = 0$, $u = 0$ when $k = 0$. For $L > 0$, $k \ne 0$ and $f$
continuous on $[0, L]$ it
[solves the fixed-traction problem](is-fixed-traction-solution-fixed-tractio.md), and for $k \ne 0$
[every solution equals it](eq-on-fixed-traction-displacement.md) on $[0, L]$.
