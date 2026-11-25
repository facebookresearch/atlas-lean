# Normalized imputed statistic

In a [second-moment imputation model](model.md) on a measure $P$ with a finite set $\iota$ of typed markers, let $w \in \mathbb{R}^\iota$ be any weights with $w^\top \Sigma_{oo} w > 0$ (for example the ridge weights solving $(\Sigma_{oo} + \lambda \mathrm{I}) w = \Sigma_{ot}$). Then the [imputed statistic](imputed.md) $\hat z = w^\top z_o$ satisfies

$$\int \Bigl(\frac{\hat z}{\sqrt{w^\top \Sigma_{oo} w}}\Bigr)^2 dP = 1.$$
