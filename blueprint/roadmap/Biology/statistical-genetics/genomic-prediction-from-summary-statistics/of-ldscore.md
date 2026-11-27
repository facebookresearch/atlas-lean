# Effect-estimate model derived from the LD-score model

Let $(h^2, \beta, \varepsilon)$ be an [LD-score model](../ld-score-regression/model.md) on a measure $\mu$ with $N$ individuals and $M$ markers, and let $X$ be a real $N \times M$ matrix with [orthogonal standardized columns](has-orthogonal-columns.md). The derived [effect-estimate model](prsmodel.md) has heritability $h^2$, sampling variance $s^2 = (1 - h^2)/N$, effects $\beta_k$, and errors

$$e_k = \frac{1}{N} \sum_{i=1}^{N} X_{ik}\, \varepsilon_i,$$

with the convention $x/0 = 0$ when $N = 0$. For $N > 0$ it describes estimation of the effects by the normalized scores $\hat\beta = X^\top y / N$.
