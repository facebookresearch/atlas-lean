# The phenotype of the LD-score model is square integrable

In every [LD-score model](../ld-score-regression/model.md) on a measure space $(\Omega, \mu)$, and
for every real $N \times M$ genotype matrix $X$, each
[phenotype](../ld-score-regression/pheno.md)

$$y_i = \sum_{k=1}^{M} X_{ik} \beta_k + \varepsilon_i$$

belongs to $L^2(\mu)$: it is almost everywhere measurable and $\int |y_i|^2 \, d\mu < \infty$.
This uses only that the model's effects $\beta_k$ and noise terms $\varepsilon_i$ are square
integrable; $\mu$ need not be finite.
