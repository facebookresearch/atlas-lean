# Weighted residual sum of squares of a line

For a finite set $\iota$ of SNPs, weights $v$, associations $\hat\beta_X, \hat\beta_Y$ in $\mathbb{R}^\iota$, an intercept $a$ and a slope $b$, the weighted residual sum of squares is

$$S_E(a, b) = \sum_{j \in \iota} v_j\, (\hat\beta_{Yj} - a - b\, \hat\beta_{Xj})^2.$$
