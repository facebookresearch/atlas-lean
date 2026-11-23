# Posterior of the selection coefficient is stochastically nonincreasing in the PTV count

Let $\mu$ be a measure on $\mathbb{R}$ with $\mu(\mathbb{R} \setminus (0, \infty)) = 0$, and let $\lambda : \mathbb{R} \to \mathbb{R}$ be nonincreasing and nonnegative on $(0, \infty)$. For a natural number $k$ write $L_k(s) = e^{-\lambda(s)} \lambda(s)^k / k!$ for the Poisson likelihood of $k$ at mean $\lambda(s)$, and suppose that every $L_k$ is $\mu$-integrable. Let $k \le k'$ be natural numbers with $\int L_k \, d\mu > 0$ and $\int L_{k'} \, d\mu > 0$. Then for every real $t$,

$$\frac{\int_{(t, \infty)} L_{k'} \, d\mu}{\int L_{k'} \, d\mu} \le \frac{\int_{(t, \infty)} L_{k} \, d\mu}{\int L_{k} \, d\mu}.$$

When $\mu$ is a prior on the heterozygous selection coefficient $s_{\mathrm{het}}$ and the observed PTV count is Poisson with mean $\lambda(s_{\mathrm{het}})$, the two sides are the posterior probabilities of $s_{\mathrm{het}} > t$ given $k'$ and given $k$: observing more PTVs never raises the posterior probability of strong selection.
