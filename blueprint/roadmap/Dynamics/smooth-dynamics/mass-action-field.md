# Mass-action vector field

Let $N$ be a [chemical reaction network](reaction-network.md) with finite species set $S$ and finite reaction set $\rho$, and let $k \in \mathbb{R}^\rho$ be rate constants. The mass-action vector field is
the map $f \colon \mathbb{R}^S \to \mathbb{R}^S$,

$$f(x) = \sum_{r \in \rho} k_r \left(\prod_{s' \in S} x_{s'}^{\mathrm{src}(r)_{s'}}\right) \bigl(\mathrm{prod}(r) - \mathrm{src}(r)\bigr).$$
