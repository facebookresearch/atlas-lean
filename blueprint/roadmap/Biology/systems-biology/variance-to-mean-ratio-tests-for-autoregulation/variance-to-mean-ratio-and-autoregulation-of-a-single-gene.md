# Variance-to-mean ratio and autoregulation of a single gene

Let $X(t)\in\{0,1,2,\dots\}$ be the mRNA (or protein) count of a gene whose expression is autonomous, modelled as a birth–death Markov chain with transition rate $f_n\ge0$ from $n-1$ to $n$ and per-molecule degradation rate $g_n>0$, so the rate from $n$ to $n-1$ is $ng_n$:

$$\frac{d}{dt}P[X=n]=P[X=n+1]\,g_{n+1}(n+1)+P[X=n-1]\,f_n-P[X=n]\,(f_{n+1}+g_nn).$$

Let $h_n=f_n/g_n$ be the relative growth rate, and assume a stationary distribution $P_n$ with finite mean and variance exists, so $P_n=P_{n-1}h_n/n$. The gene has positive (negative) autoregulation if $h_{n+1}>h_n$ ($h_{n+1}<h_n$) for some $n$; with no autoregulation $h_n\equiv h$ and $X$ is Poisson($h$). Let $\mathrm{VMR}(X)=\mathrm{Var}(X)/\mathbb E(X)$ at stationarity.

**Lemma.** If $h_{n+1}\ge h_n$ for all $n$, then $\mathrm{VMR}(X)\ge1$; if $h_{n+1}\le h_n$ for all $n$, then $\mathrm{VMR}(X)\le1$; in either case equality holds iff $h_n$ is constant.

**Proposition.** Consequently, $\mathrm{VMR}(X)>1$ implies positive autoregulation at some level, $\mathrm{VMR}(X)<1$ implies negative autoregulation at some level, and $\mathrm{VMR}(X)=1$ means either no autoregulation or both signs at different levels. No assumption on the degradation rates $g_n$ is needed.

**Example.** For $f_n=k+b(n-1)$ and $g_n=c$ with $c>0$, $c-b>0$, $\mathrm{VMR}=1+b/(c-b)$, so the sign of $\mathrm{VMR}-1$ is the sign of the feedback strength $b$.

## Expansion

From $nP_n=h_nP_{n-1}$ one gets $\mathbb E[X]=\mathbb E[h_{X+1}]$ and $\mathbb E[X^2]=\mathbb E[(X+1)h_{X+1}]$, hence

$$\mathrm{Var}(X)-\mathbb E[X]=\mathbb E[Xh_{X+1}]-\mathbb E[X]\,\mathbb E[h_{X+1}]=\mathrm{Cov}\big(X,h_{X+1}\big).$$

So $\mathrm{VMR}-1=\mathrm{Cov}(X,h_{X+1})/\mathbb E[X]$. If $n\mapsto h_{n+1}$ is nondecreasing (nonincreasing), the covariance of $X$ with a monotone function of itself is nonnegative (nonpositive) by Chebyshev's association inequality, and it vanishes only when that function is constant on the support. The Proposition is the contrapositive. This identity is one short route to the Lemma; the paper argues through $P_n=P_0\prod_{i\le n}h_i/n!$.

## Sources

- Y. Wang, S. He, "Inference on autoregulation in gene expression with variance-to-mean ratio", Journal of Mathematical Biology (2023), single-gene setup (Eq. (1)), Example 1, Lemma 1, Proposition 1 and the proof of Lemma 1, <https://doi.org/10.1007/s00285-023-01924-6>, PMCID PMC10154285.
