# IVW estimator minimizes the weighted residual sum of squares

For every finite set $\iota$ of SNPs, all data $\hat\beta_X, \hat\beta_Y, \sigma \in \mathbb{R}^\iota$ and every $b \in \mathbb{R}$,

$$S(\hat\beta_{\mathrm{IVW}}) \le S(b),$$

where $S$ is the [weighted residual sum of squares through the origin](weighted-ssr.md) and $\hat\beta_{\mathrm{IVW}}$ the [IVW estimator](ivw.md) (with the convention $x/0 = 0$ throughout).
