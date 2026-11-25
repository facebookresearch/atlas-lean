# Proportional lift on a nonzero-capacity endpoint class

Let $V$ and $E$ be finite sets and let each arc $e \in E$ run from its tail $t(e) \in V$ to its head $h(e) \in V$; parallel arcs and loops are allowed. For $f : E \to \mathbb{R}$ write $\bar f(p, q) = \sum_{e \,:\, t(e) = p,\ h(e) = q} f(e)$ for the total of $f$ over the arcs from $p$ to $q$. Let $u : E \to \mathbb{R}$, $F : V \times V \to \mathbb{R}$ and let $\hat F : E \to \mathbb{R}$ be the proportional lift of $F$, $\hat F(e) = F(t(e), h(e))\, u(e) / \bar u(t(e), h(e))$ when $\bar u(t(e), h(e)) \ne 0$ and $\hat F(e) = 0$ otherwise. If $\bar u(t(e), h(e)) \ne 0$ for an arc $e$, then

$$\hat F(e) = \frac{F(t(e), h(e))\, u(e)}{\bar u(t(e), h(e))}.$$
