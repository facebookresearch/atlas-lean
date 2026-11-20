# The Q-criterion of a split-decomposed dissimilarity

Let $X$ be a finite set, $(A_e)_{e \in E}$ a finite family of subsets with real weights $w_e$, and $d(x, y) = \frac12 \sum_{e \,:\, A_e \text{ separates } x, y} w_e$. Then for all $x, y$,

$$(|X| - 2) d(x, y) - \sum_z d(x, z) - \sum_z d(y, z) = -\sum_e w_e\, g_{A_e}(x, y),$$

where $g$ is the [split contribution](split-gain.md).
