# KL divergence bound between SFS distributions of size histories

**Setting.** Under Kingman's coalescent with deterministic population size $\eta:[0,\infty)\to(0,\infty)$ (pairwise coalescence rate $1/\eta(t)$ at time $t$ in the past) and infinite-sites mutation with known ancestral allele, let $q^{(\eta)}_{n,b}$ be the probability that a segregating site carries $b$ derived alleles in a sample of $n$, $1\le b\le n-1$. With $a_m=\binom m2$ and $R_\eta(t)=\int_0^t\eta(u)^{-1}du$, the expected time to the first coalescence among $m$ lineages is

$$
c^{(\eta)}_m=\int_0^\infty t\,\frac{a_m}{\eta(t)}\,e^{-a_mR_\eta(t)}\,dt,
$$

and there are universal constant vectors $\mathbf W_{n,b}$, $\mathbf V_n=\sum_b\mathbf W_{n,b}$ (independent of $\eta$) such that $q^{(\eta)}_{n,b}=\langle\mathbf c^{(\eta)},\mathbf W_{n,b}\rangle/\langle\mathbf c^{(\eta)},\mathbf V_n\rangle$, where $\mathbf c^{(\eta)}=(c^{(\eta)}_2,\dots,c^{(\eta)}_n)$; here $\langle\mathbf c^{(\eta)},\mathbf V_n\rangle$ is the expected total tree length. Write $D(\eta\,\|\,\eta')$ for the Kullback–Leibler divergence between the SFS distributions $q^{(\eta)}_n$ and $q^{(\eta')}_n$.

**Theorem (general bound).** If $\eta(t)=\eta'(t)$ for $0\le t\le t_c$ and $\max_{t>t_c}\eta(t)\le\min_{t>t_c}\eta'(t)$, then

$$
D(\eta\,\|\,\eta')\le\frac{\langle\mathbf c^{(\eta')}-\mathbf c^{(\eta)},\mathbf V_n\rangle}{\langle\mathbf c^{(\eta)},\mathbf V_n\rangle}.
$$

**Bottleneck family.** Fix change points $t_1<\dots<t_{I+J-1}$ and sizes of the first $I$ epochs, the $I$th being the smallest, $\varepsilon=N_I$ (the bottleneck), lasting $t_b=t_I-t_{I-1}$. On $[t_I,t_{I+1})$ the size is $h$ or $h+\delta$ with $h>\varepsilon$, $\delta>0$, and at each later change point it stays or jumps up by $\delta$; this gives a family $\mathcal M_{I,J}$ of $2^J$ piecewise-constant histories. For all $\eta,\eta'\in\mathcal M_{I,J}$,

$$
\big|c^{(\eta)}_m-c^{(\eta')}_m\big|\le J\,\frac{\delta}{a_m}\,e^{-a_mt_b/\varepsilon},
$$

and if moreover $\max_{t\ge t_I}\eta(t)\le\min_{t\ge t_I}\eta'(t)$, then

$$
D(\eta\,\|\,\eta')\le J\,\frac{\delta}{\varepsilon}\,e^{-t_b/\varepsilon}.
$$

The bound does not depend on the sample size $n$: a lineage survives the bottleneck uncoalesced with probability about $e^{-a_mt_b/\varepsilon}$, so the pre-bottleneck history leaves an exponentially faint trace in the SFS.

## Depends on

- [Expected site frequency spectrum under variable population size](../variable-sfs.md)

## Expansion

For the general bound, use $q_{n,b}=\langle\mathbf c,\mathbf W_{n,b}\rangle/\langle\mathbf c,\mathbf V_n\rangle$ and $\log x\le x-1$ to bound $D\le\sum_b q^{(\eta)}_{n,b}\big(q^{(\eta)}_{n,b}/q^{(\eta')}_{n,b}-1\big)$. Under the stated ordering, coalescence under $\eta'$ is stochastically later after $t_c$, so each entry of $\mathbf c^{(\eta')}-\mathbf c^{(\eta)}$ is nonnegative, and the ratio of total lengths gives the bound. For the bottleneck family, the piecewise formula $c^{(\eta)}_m=a_m^{-1}\sum_kN_k\big(e^{-a_mS_{k-1}}-e^{-a_mS_k}\big)$ with $S_k=\sum_{j\le k}(t_j-t_{j-1})/N_j$ shows that the histories differ only through terms carrying the factor $e^{-a_mS_I}\le e^{-a_mt_b/\varepsilon}$, each multiplied by at most $J\delta$. Summing against $\mathbf V_n$ and using that $\sum_m V_{n,m}/a_m=2H_{n-1}$ is the expected tree length at constant size $1$ gives $\langle\mathbf c^{(\eta')}-\mathbf c^{(\eta)},\mathbf V_n\rangle\le 2J\delta H_{n-1}e^{-t_b/\varepsilon}$, where $H_{n-1}=\sum_{b<n}1/b$. Since $\min_t\eta(t)=\varepsilon$, the expected tree length is at least its value $2\varepsilon H_{n-1}$ at constant size $\varepsilon$; the harmonic numbers cancel, which is why the bound is free of $n$.

## Sources

- Jonathan Terhorst and Yun S. Song, *Fundamental limits on the accuracy of demographic inference based on the sample frequency spectrum*, *Proceedings of the National Academy of Sciences* 112 (2015), 7677–7682, <https://doi.org/10.1073/pnas.1503717112>; preprint arXiv:1505.04228, <https://doi.org/10.48550/arXiv.1505.04228>. Numbering of the arXiv version: Theorem 1, Lemma 2, Theorem 3; setting in Section 2.
