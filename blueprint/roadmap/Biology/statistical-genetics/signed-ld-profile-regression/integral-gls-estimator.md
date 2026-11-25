# Unbiasedness of the weighted least-squares estimator

Let a [first-moment SLDP model](model.md) on a measure $P$ have mean effects $m = \mu v$ with $\mu \in \mathbb{R}$ and $v \in \mathbb{R}^M$, let $X$ be a real $N \times M$ genotype matrix, let $W$ be a real $M \times M$ matrix, and let $s = \hat R v$ be the signed LD profile of $v$, where $\hat R$ is the [in-sample LD matrix](ld-matrix.md). If $s^\top W s \ne 0$, then

$$\int \frac{s^\top W \hat\alpha}{s^\top W s} \, dP = \mu,$$

where $\hat\alpha$ is the vector of [normalized marginal scores](alpha-hat.md). SLDP regression uses as $W$ the inverse of $\sigma^2 R^2 + R/N$.
