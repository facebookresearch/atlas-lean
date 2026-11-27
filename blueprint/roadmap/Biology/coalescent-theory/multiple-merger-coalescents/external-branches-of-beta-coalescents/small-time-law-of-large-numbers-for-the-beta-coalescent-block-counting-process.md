# Small-time law of large numbers for the Beta-coalescent block-counting process

Let $\Lambda$ be a finite measure on $[0,1]$ and $\Pi^{(n)}$ the $\Lambda$-$n$-coalescent, in which any $k$ of $b$ blocks merge at rate $\lambda_{b,k}=\int_0^1x^{k-2}(1-x)^{b-k}\Lambda(dx)$. Let $R^{(n)}_t=|\Pi^{(n)}_t|$ be its block-counting process, started from $R^{(n)}_0=n$. Set $\rho(t)=\int_t^1x^{-2}\Lambda(dx)$ and assume

$$
\rho(t)=C_0t^{-\alpha}+O(t^{-\alpha+\zeta})\qquad (t\to0)
$$

for some $C_0>0$, $\alpha\in(1,2)$ and $\zeta>1-1/\alpha$. This class contains every $\mathrm{Beta}(a,b)$-coalescent with $a\in(0,1)$, $b>0$; for $\mathrm{Beta}(2-\alpha,\alpha)$, $C_0\Gamma(2-\alpha)=1/(\alpha\Gamma(\alpha))$.

**Theorem.** For every $t_0>0$ and $\varepsilon>0$,

$$
\mathbb P\Big(\sup_{0\le t\le t_0}\Big|\,n^{-1}R^{(n)}_{tn^{1-\alpha}}-\big(1+C_0\Gamma(2-\alpha)\,t\big)^{-1/(\alpha-1)}\Big|>\varepsilon\Big)\longrightarrow0\qquad(n\to\infty).
$$

**Kingman case.** For Kingman's $n$-coalescent ($\Lambda=\delta_0$), for every $t_0>0$ and $\varepsilon>0$,

$$
\mathbb P\Big(\sup_{0\le t\le t_0}\big|\,n^{-1}R^{(n)}_{t/n}-(1+t/2)^{-1}\big|>\varepsilon\Big)\longrightarrow0,
$$

which is the formal $\alpha=2$, $C_0\Gamma(2-\alpha)=1/2$ case of the Beta formula.

So, on time scale $n^{1-\alpha}$, the fraction of surviving lineages follows the deterministic solution of $\dot r=-\frac{C_0\Gamma(2-\alpha)}{\alpha-1}\,r^{\alpha}$, $r(0)=1$.

## Depends on

- [The Λ-coalescent rate matrix on partitions of a finite sample](../../coalescents/the-coalescent-rate-matrix-on-partitions-of-a-fi.md)

## Expansion

With $k$ blocks, the total collision rate is $g_k=k(k-1)\int_0^1(1-t)^{k-2}t\,\rho(t)\,dt\sim C_0\Gamma(2-\alpha)k^{\alpha}$, and the number of blocks lost per collision converges in law to a variable with mean $1/(\alpha-1)$ and heavy tail of index $\alpha$. Writing the jump chain as a random walk, the number of blocks after $\lfloor ns\rfloor$ collisions is close to $n(1-s/(\alpha-1))$, with $\alpha$-stable fluctuations of smaller order. Summing the exponential holding times $1/g_k$ along this path, the elapsed time after $\lfloor ns\rfloor$ collisions, multiplied by $n^{\alpha-1}$, converges to $\frac{1}{C_0\Gamma(2-\alpha)}\big((1-\frac{s}{\alpha-1})^{1-\alpha}-1\big)$; inverting this time change gives the stated profile.

## Sources

- Jean-Stéphane Dhersin, Fabian Freund, Arno Siri-Jégousse and Linglong Yuan, *On the length of an external branch in the Beta-coalescent*, *Stochastic Processes and their Applications* 123 (2013), 1691–1715, <https://doi.org/10.1016/j.spa.2012.12.010>; preprint arXiv:1201.3983, <https://doi.org/10.48550/arXiv.1201.3983>. Numbering of the arXiv version: Theorems 4.4 and 4.5, Proposition 4.1, Section 2.
