# Confounded design: the data depend only on $\beta + \delta$

Let $E \in \mathbb{R}^{n \times p}$, $\mu, \beta, \delta \in \mathbb{R}^p$ and $b \in \mathbb{R}^n$.
In the confounded [additive design](batch-model.md), where the biological covariate equals the batch
covariate $b$,

$$E + \mathbf 1 \mu^\top + b \beta^\top + b \delta^\top
= E + \mathbf 1 \mu^\top + b (\beta + \delta)^\top.$$

The data matrix is the design with batch effect $\beta + \delta$ and biological signal $0$: it
depends on $(\beta, \delta)$ only through $\beta + \delta$.
