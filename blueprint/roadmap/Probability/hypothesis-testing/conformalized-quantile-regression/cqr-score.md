# CQR conformity score

Let $\mathcal{X}$ be a set and $q_{\mathrm{lo}}, q_{\mathrm{hi}} : \mathcal{X} \to \mathbb{R}$ fitted lower and upper conditional quantile functions. The CQR score of a data point $(x, y) \in \mathcal{X} \times \mathbb{R}$ is

$$E(x, y) = \max\big(q_{\mathrm{lo}}(x) - y,\ y - q_{\mathrm{hi}}(x)\big):$$

the formula applies to arbitrary functions $q_{\mathrm{lo}}, q_{\mathrm{hi}}$. When $q_{\mathrm{lo}}(x) \le q_{\mathrm{hi}}(x)$, the score is minus the distance from $y$ to the nearer endpoint when $y \in [q_{\mathrm{lo}}(x), q_{\mathrm{hi}}(x)]$, so negative strictly inside, and the distance to the nearer endpoint otherwise.

## Sources

- Y. Romano, E. Patterson and E. J. Candès, *Conformalized quantile regression*, NeurIPS 2019, arXiv:1905.03222, Algorithm 1 (the scores $E_i$).
