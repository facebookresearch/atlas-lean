# The constructed displacement has the load-path strain as derivative

Let $L > 0$, let $f \colon \mathbb{R} \to \mathbb{R}$ be continuous on $[0, L]$, and let $k$ and $P$
be any real numbers. For every $x \in [0, L]$, the derivative within $[0, L]$ (one-sided at the
ends) of the [fixed-traction displacement](fixed-traction-displacement.md)
$u(x) = \int_0^x \varepsilon(y)\, dy$ is the [load-path strain](fixed-traction-strain.md)

$$u'(x) = \varepsilon(x) = \frac{1}{k}\left(P + \int_x^L f(y)\, dy\right).$$

No condition on $k$ is needed: for $k = 0$ both sides are $0$, by the convention $a/0 = 0$.
