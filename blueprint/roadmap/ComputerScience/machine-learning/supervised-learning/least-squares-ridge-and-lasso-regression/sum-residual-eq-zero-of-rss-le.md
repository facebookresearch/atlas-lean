# Least-squares residuals sum to zero with an intercept

Let $X$ be a real $m \times \iota$ design matrix with a finite column index type $\iota$, $y \in \mathbb{R}^m$, and let $\theta \in \mathbb{R}^\iota$ minimize the residual sum of squares $\mathrm{RSS}(\theta') = (y - X\theta') \cdot (y - X\theta')$ over all $\theta' \in \mathbb{R}^\iota$. If $X$ has an intercept column $j$ ($X_{kj} = 1$ for every row $k$), then the residuals sum to zero:

$$\sum_{k} (y - X\theta)_k = 0 .$$

## Sources

J. M. Wooldridge, *Introductory Econometrics: A Modern Approach*, 7th ed., Cengage Learning, 2020, Sections 2.3 and 3.2 (algebraic properties of OLS: with an intercept, the residuals sum to zero).
