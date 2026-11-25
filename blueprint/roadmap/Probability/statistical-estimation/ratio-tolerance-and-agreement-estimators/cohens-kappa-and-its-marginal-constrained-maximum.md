# Cohen's kappa and its maximum for fixed margins

Let two raters classify items into $k$ categories with joint proportions $p_{ij}$ and margins $p_{i\cdot}$, $p_{\cdot j}$, let $p_o = \sum_i p_{ii}$ be the observed agreement and $p_e = \sum_i p_{i\cdot}\, p_{\cdot i}$ the agreement expected from the margins, with $p_e < 1$. Cohen's kappa is $\kappa = (p_o - p_e)/(1 - p_e)$; it equals $1$ under complete agreement, $0$ when agreement is what the margins alone give, and can be negative (Cohen's kappa, Wikipedia). Since $p_{ii} \le \min(p_{i\cdot}, p_{\cdot i})$,

$$\kappa \le \kappa_{\max} = \frac{\sum_i \min(p_{i\cdot}, p_{\cdot i}) - p_e}{1 - p_e},$$

and the bound is attained by a joint table with the given margins: put $\min(p_{i\cdot}, p_{\cdot i})$ on the diagonal; the residual row sum of category $i$ is positive only if $p_{i\cdot} > p_{\cdot i}$, in which case its residual column sum is zero, so the rows and columns with positive residuals are disjoint and can be filled off the diagonal (for example by the product of the residual margins divided by their common total).

## Expansion

1. The model: a joint law on $k \times k$ categories, agreement $p_o$ and chance agreement $p_e$.
2. The values $\kappa = 1$ under complete agreement and $\kappa = 0$ under independence with the given margins.
3. The bound $\kappa_{\max}$ and its attainment by the diagonal-minimum table.
4. The minimum of $\kappa$ for fixed margins, and the limitations of kappa's baseline discussed in the source, as separate statements.

## Sources

- Cohen's kappa, Wikipedia, sections on the definition and on limitations. <https://en.wikipedia.org/wiki/Cohen%27s_kappa>
- Original result: J. Cohen, A coefficient of agreement for nominal scales, Educ. Psychol. Meas. 20 (1960), 37–46. <https://doi.org/10.1177/001316446002000104> The definition follows Cohen's kappa, Wikipedia.
