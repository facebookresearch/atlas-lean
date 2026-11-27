# MR-Egger slope under pleiotropy

Let $\iota$ be a finite set of SNPs, let $v, \gamma \in \mathbb{R}^\iota$ with $\operatorname{Var}_v(\gamma) \ne 0$, let $\alpha \in \mathbb{R}^\iota$ (pleiotropic terms) and $\beta \in \mathbb{R}$, and put $\Gamma_j = \alpha_j + \beta \gamma_j$. Then the [MR-Egger slope](egger-slope.md) of $\Gamma$ on $\gamma$ is (Bowden, Davey Smith & Burgess 2015)

$$b_E = \beta + \frac{\operatorname{Cov}_v(\gamma, \alpha)}{\operatorname{Var}_v(\gamma)}.$$

## Sources

- J. Bowden, G. Davey Smith, S. Burgess, *Mendelian randomization with invalid instruments: effect estimation and bias detection through Egger regression*, Int. J. Epidemiol. 44 (2015), 512–525.
