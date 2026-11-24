# Mean squared imputation error

In every [second-moment imputation model](model.md) on a measure $P$ with a finite set $\iota$ of typed markers, and for all weights $w \in \mathbb{R}^\iota$, the [imputed statistic](imputed.md) $\hat z = w^\top z_o$ satisfies

$$\int (z_t - \hat z)^2 \, dP = \Sigma_{tt} - 2\, w^\top \Sigma_{ot} + w^\top \Sigma_{oo} w.$$
