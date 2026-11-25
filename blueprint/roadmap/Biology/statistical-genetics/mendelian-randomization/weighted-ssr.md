# Weighted residual sum of squares through the origin

For a finite set $\iota$ of SNPs with data $\hat\beta_X, \hat\beta_Y, \sigma \in \mathbb{R}^\iota$ and a slope $b \in \mathbb{R}$, the weighted residual sum of squares is

$$S(b) = \sum_{j \in \iota} \frac{(\hat\beta_{Yj} - b\, \hat\beta_{Xj})^2}{\sigma_j^2},$$

with the convention $x/0 = 0$.
