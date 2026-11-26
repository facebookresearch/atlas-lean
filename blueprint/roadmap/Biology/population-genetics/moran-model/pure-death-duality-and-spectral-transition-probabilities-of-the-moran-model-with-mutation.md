# Pure-death duality and spectral transition probabilities of the Moran model with mutation

**Model.** In a population of $N$ individuals of types $a$ and $A$, reproduction events occur at rate $1/2$; a uniformly chosen parent replaces a uniformly chosen individual, and the offspring mutates $a\to A$ with probability $\theta_1/N$ and $A\to a$ with probability $\theta_2/N$. The number $X^N_t\in\{0,\dots,N\}$ of $A$ individuals is a birth–death chain with rates

$$\lambda_i=\tfrac12\delta_N\Big(1-\tfrac iN\Big)\Big(\tfrac iN+\tfrac{a_N}N\Big),\qquad \mu_i=\tfrac12\delta_N\,\tfrac iN\Big(1-\tfrac iN+\tfrac{b_N}N\Big),$$

where $\delta_N=1-\theta/N$, $\theta=\theta_1+\theta_2<N$, $a_N=\theta_1/\delta_N$, $b_N=\theta_2/\delta_N$. Its stationary law is $\mathrm{BetaBin}(N,a_N,b_N)$, and it is reversible, so the generator $Q_N$ is self-adjoint in $\ell^2(\pi)$ with eigenvalues $-\gamma^N_m$,

$$\gamma^N_m=\frac{\delta_N}{2N^2}\,m\,(m+a_N+b_N-1),\qquad m=0,\dots,N .$$

**Theorem (duality).** Let $M^N$ be the pure-death process on $\{0,\dots,N\}$ that jumps $m\to m-1$ at rate $\gamma^N_m$. There are explicit kernels $K^N_m(i,j)=\sum_{\ell=0}^m\mathcal H_{N,m;i}(\ell)\,\mathcal D_{N;m,\ell}(j)$, built from hypergeometric weights $\mathcal H_{N,m;i}(\ell)$ (draw $m$ of $N$ individuals without replacement, $\ell$ of them type $A$, when $i$ are type $A$) and beta-binomial-type laws $\mathcal D_{N;m,\ell}$, such that

$$\mathbb E\big[K^N_m(X^N_t,j)\mid X^N_0=x\big]=\mathbb E\big[K^N_{M^N_t}(x,j)\mid M^N_0=m\big]\qquad(t\ge0).$$

**Theorem (transition probabilities).** For all $i,j$ and $t\ge0$,

$$\mathbb P[X^N_t=j\mid X^N_0=i]=\sum_{m=0}^Nq^N_{N,m}(t)\sum_{\ell=0}^m\mathcal H_{N,m;i}(\ell)\,\mathcal D_{N;m,\ell}(j),$$

where $q^N_{N,m}(t)=\mathbb P[M^N_t=m\mid M^N_0=N]$ is the explicit alternating sum

$$q^N_{N,m}(t)=\sum_{r=m}^N(-1)^{r-m}\frac{N!}{m!(r-m)!(N-r)!}\,\frac{2r+a_N+b_N-1}{m+r+a_N+b_N-1}\,\frac{(m+a_N+b_N)_{(N-m)}}{(m+r+a_N+b_N)_{(N-m)}}\,e^{-\gamma^N_rt}.$$

## Depends on

- [Moran and Cannings models: generator limits and effective size](moran-and-cannings-models-generator-limits-and-e.md)

## Expansion

The dual counts the lineages of a sample of the population traced back in time: $m$ lineages are lost at rate $\gamma^N_m$, combining coalescence ($\binom m2$-type terms) and mutation (linear terms). Applying $Q_N$ to the hypergeometric sampling weights gives $Q_NK^N_m=\gamma^N_m(K^N_{m-1}-K^N_m)$ by Pascal's identity, which is the pure-death generator acting on the index $m$. Starting the dual from $m=N$ (the whole population) turns duality into the stated mixture: run the lineage-counting process, then sample the remaining $m$ ancestral types from the current state and let their descendants fill the population according to the stationary Pólya-urn kernels. As $N\to\infty$ with time sped up by $N^2$, this parallels the line-of-descent representation of the Wright–Fisher diffusion transition density.

## Sources

- J. Sant, I. Valentić, "From invasion to replacement: excursions of the Moran model", arXiv:2611.31663 (2026), Section 2 (rates, Proposition 1, Theorems 1 and 2), <https://doi.org/10.48550/arXiv.2611.31663>.
