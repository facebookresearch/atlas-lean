# Twice the Wirtinger derivative of a sum of radial primitives

Let $s$ be a finite index set and, for $\alpha \in s$, let $f_\alpha : \mathbb{R} \to \mathbb{R}$ be continuous on $[0, \infty)$ with $f_\alpha(0) = 0$ and let $z_\alpha \in \mathbb{C}$. Let $W(w) = \sum_{\alpha \in s} \int_0^{|w - z_\alpha|} f_\alpha(t)\, dt$, a real-valued function on $\mathbb{C}$, and let $\partial_{\bar z} W = \frac12 (\partial_x W + i\, \partial_y W)$. Then for every $z \in \mathbb{C}$,

$$
2\, \partial_{\bar z} W(z) = \sum_{\alpha \in s} \frac{f_\alpha(|z - z_\alpha|)}{|z - z_\alpha|} (z - z_\alpha).
$$

Each summand is $0$ at its own centre $z_\alpha$ (the quotient being read as $0$ there); the sum need not vanish there.
