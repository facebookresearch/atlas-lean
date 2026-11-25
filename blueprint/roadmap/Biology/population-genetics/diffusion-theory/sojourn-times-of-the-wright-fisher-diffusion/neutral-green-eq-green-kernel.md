# Neutral Green's function as a two-solution Green kernel

For $p, x \in (0, 1)$, the [neutral Green's function](neutral-green.md) is the two-solution Green
kernel built from the left solution $u(x) = 1/(1 - x)$, the right solution $v(x) = 1/x$ and the
coefficient $C(p) = 2(1 - p)$:

$$
G(p, x) = C(p)\, u(x) = \frac{2(1 - p)}{1 - x} \ \text{ if } x \le p, \qquad
G(p, x) = C(p)\, \frac{u(p)}{v(p)}\, v(x) = \frac{2p}{x} \ \text{ if } p < x.
$$
