# MR-Egger intercept under pleiotropy

Let $\iota$ be a finite set of SNPs, let $v, \gamma \in \mathbb{R}^\iota$ with $\operatorname{Var}_v(\gamma) \ne 0$, let $\alpha \in \mathbb{R}^\iota$ and $\beta \in \mathbb{R}$, and put $\Gamma_j = \alpha_j + \beta \gamma_j$. Then the [MR-Egger intercept](egger-intercept.md) of $\Gamma$ on $\gamma$ is

$$a_E = \bar\alpha_v - \frac{\operatorname{Cov}_v(\gamma, \alpha)}{\operatorname{Var}_v(\gamma)}\, \bar\gamma_v,$$

where the bars denote [weighted means](weighted-mean.md).
