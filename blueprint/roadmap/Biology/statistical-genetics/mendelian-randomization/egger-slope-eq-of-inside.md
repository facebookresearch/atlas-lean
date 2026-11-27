# InSIDE identity for MR-Egger

Let $\iota$ be a finite set of SNPs, let $v, \gamma, \alpha \in \mathbb{R}^\iota$ with $\operatorname{Var}_v(\gamma) \ne 0$ and $\operatorname{Cov}_v(\alpha, \gamma) = 0$ (the weighted InSIDE condition), let $\beta \in \mathbb{R}$, and put $\Gamma_j = \alpha_j + \beta \gamma_j$. Then for the MR-Egger regression of $\Gamma$ on $\gamma$ (Bowden, Davey Smith & Burgess 2015):

- the [slope](egger-slope.md) is $b_E = \beta$;
- the [intercept](egger-intercept.md) is $a_E = \bar\alpha_v$, the [weighted mean](weighted-mean.md) of the pleiotropic terms.

## Sources

- J. Bowden, G. Davey Smith, S. Burgess, *Mendelian randomization with invalid instruments: effect estimation and bias detection through Egger regression*, Int. J. Epidemiol. 44 (2015), 512–525.
