# Mean squared error of imputation with ImpG weights

In a [second-moment imputation model](model.md) on a measure $P$ with a finite set $\iota$ of typed markers, let $w \in \mathbb{R}^\iota$ satisfy $\Sigma_{oo} w = \Sigma_{ot}$. Then the [imputed statistic](imputed.md) $\hat z = w^\top z_o$ satisfies

$$\int (z_t - \hat z)^2 \, dP = \Sigma_{tt} - w^\top \Sigma_{ot},$$

the second moment of the linear-prediction error. For centred statistics under a probability measure it is the residual variance of the linear prediction, and the conditional variance only when the statistics are moreover jointly Gaussian.
