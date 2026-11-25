# MR-Egger slope

For a finite set $\iota$ of SNPs, weights $v$ and associations $\hat\beta_X, \hat\beta_Y$ in $\mathbb{R}^\iota$, the MR-Egger slope is

$$b_E = \frac{\operatorname{Cov}_v(\hat\beta_X, \hat\beta_Y)}{\operatorname{Var}_v(\hat\beta_X)},$$

with the [weighted covariance](weighted-cov.md) and the convention $x/0 = 0$. For nonnegative weights with positive sum and $\operatorname{Var}_v(\hat\beta_X) > 0$, it is the slope of the weighted least-squares regression of $\hat\beta_Y$ on $\hat\beta_X$ with an intercept. Bowden, Davey Smith and Burgess (2015) use the weights $v_j = \sigma_j^{-2}$.

## Sources

- J. Bowden, G. Davey Smith and S. Burgess, *Mendelian randomization with invalid instruments: effect estimation and bias detection through Egger regression*, Int. J. Epidemiol. 44 (2015), 512–525.
