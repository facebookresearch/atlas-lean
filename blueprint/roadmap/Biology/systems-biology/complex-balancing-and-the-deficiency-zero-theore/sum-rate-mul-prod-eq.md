# Complex balance exchanges source and product sums

Let $N$ be a [chemical reaction network](reaction-network.md) with finite species set $S$ and finite reaction set $\rho$. Let $k \in \mathbb{R}^\rho$ and $c \in \mathbb{R}^S$, with $c$
[complex balanced](is-complex-balanced.md) for $k$. Then for every function
$g \colon \mathbb{N}^S \to \mathbb{R}$,

$$\sum_{r \in \rho} v_r\, g(\mathrm{prod}(r)) = \sum_{r \in \rho} v_r\, g(\mathrm{src}(r)),$$

where $v_r = k_r \prod_s c_s^{\mathrm{src}(r)_s}$ is the [mass-action rate](rate.md) of reaction $r$.
