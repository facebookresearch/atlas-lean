# Posterior of the selection coefficient in the Cassa et al. model

Let $\mu$ be a probability measure on $\mathbb{R}$ with $\mu((0, \infty)) = 1$, let $n > 0$ and $U > 0$, and let $L_k(s) = e^{-\lambda(s)} \lambda(s)^k / k!$ with $\lambda(s) = nU/s$ the [balance mean](balance-mean.md). Then for all natural numbers $k \le k'$ and every real $t$ (Cassa et al. 2017),

$$\frac{\int_{(t, \infty)} L_{k'} \, d\mu}{\int L_{k'} \, d\mu} \le \frac{\int_{(t, \infty)} L_{k} \, d\mu}{\int L_{k} \, d\mu},$$

with the convention $x/0 = 0$: the posterior probability $P(s_{\mathrm{het}} > t \mid k)$ is nonincreasing in the observed PTV count $k$, for every prior on $(0, \infty)$.

## Sources

- C. A. Cassa et al., *Estimating the selective effects of heterozygous protein-truncating variants from human exome data*, Nat. Genet. 49 (2017), 806–810.
