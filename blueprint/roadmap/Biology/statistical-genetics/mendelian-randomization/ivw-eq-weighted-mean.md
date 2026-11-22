# IVW estimator as a weighted mean of ratio estimates

For every finite set $\iota$ of SNPs and all data $\hat\beta_X, \hat\beta_Y, \sigma \in \mathbb{R}^\iota$,

$$\hat\beta_{\mathrm{IVW}} = \frac{\sum_j w_j\, \hat\beta_{Yj} / \hat\beta_{Xj}}{\sum_j w_j},$$

where $\hat\beta_{\mathrm{IVW}}$ is the [IVW estimator](ivw.md), $w_j$ the [inverse-variance weights](ivw-weight.md) and $\hat\beta_{Yj}/\hat\beta_{Xj}$ the [ratio estimates](ratio-estimate.md), with the convention $x/0 = 0$.
