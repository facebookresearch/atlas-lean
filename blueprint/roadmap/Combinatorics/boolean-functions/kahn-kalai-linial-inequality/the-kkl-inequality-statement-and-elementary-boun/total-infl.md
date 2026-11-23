# Total influence under a product weight

Let $E$ be a finite set, $\nu = (\nu_e)_{e \in E}$ a family of weights $\nu_e : \{0, 1\} \to \mathbb{R}$ and $g : \{0, 1\}^E \to \mathbb{R}$. The total influence of $g$ is

$$\sum_{e \in E} \mathrm{Inf}_e(g), \qquad \mathrm{Inf}_e(g) = \mathbb{E}_\nu\big\lvert g(\omega^{e \to 1}) - g(\omega^{e \to 0})\big\rvert,$$

where $\mathrm{Inf}_e$ is the [influence](../../osss-inequality-for-decision-trees/infl.md) under the product weight $\nu$.
