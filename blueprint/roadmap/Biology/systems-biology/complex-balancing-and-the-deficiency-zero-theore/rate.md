# Mass-action reaction rate

Let $N$ be a [chemical reaction network](reaction-network.md) with species set $S$ and reaction set $\rho$, with $S$ finite. For rate constants $k \in \mathbb{R}^\rho$ and concentrations
$c \in \mathbb{R}^S$, the mass-action rate of reaction $r$ is
$k_r \prod_{s \in S} c_s^{\mathrm{src}(r)_s}$.
