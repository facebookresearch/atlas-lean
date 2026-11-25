# Second moment of the statistic imputed with ImpG weights

In a [second-moment imputation model](model.md) on a measure $P$ with a finite set $\iota$ of typed markers, let $w \in \mathbb{R}^\iota$ satisfy the normal equations $\Sigma_{oo} w = \Sigma_{ot}$ (the ImpG weights; $w = \Sigma_{oo}^{-1} \Sigma_{ot}$ when $\Sigma_{oo}$ is invertible). Then the [imputed statistic](imputed.md) $\hat z = w^\top z_o$ satisfies

$$\int \hat z^{\,2} \, dP = w^\top \Sigma_{ot}.$$

In general this is the explained second moment. For centred statistics under a probability measure and $\Sigma_{tt} = 1$, it is one minus the linear-prediction residual variance, the imputation accuracy $r^2_{\mathrm{pred}}$ of ImpG.
