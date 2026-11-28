# Size scaling of survival from identical independent pieces

Let $V, V_0 \in \mathbb{R}$ with $V / V_0 = m \in \mathbb{N}$, and let $\mathrm{specimen}, S_{\mathrm{ref}} : \mathbb{R} \to \mathbb{R}$ and $\mathrm{piece}_i : \mathbb{R} \to \mathbb{R}$ ($i \in \mathbb{N}$) be functions. Suppose the specimen survival is the product of the survivals of $m$ pieces,

$$\mathrm{specimen}(x) = \prod_{i=0}^{m-1} \mathrm{piece}_i(x) \quad \text{for all } x,$$

and each piece has the reference survival: $\mathrm{piece}_i(x) = S_{\mathrm{ref}}(x)$ for all $i < m$ and all $x$. Then for every $x$,

$$\mathrm{specimen}(x) = S_{\mathrm{ref}}(x)^{V / V_0},$$

a real power. The product hypothesis encodes independence of the pieces; no form of the hazard is assumed.

The value $V_0 = 0$ is allowed: then $V / V_0 = 0$ by the convention $x / 0 = 0$, so $m = 0$, the empty product is $1$, and both sides equal $1$.
