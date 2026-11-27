# Mittag-Leffler limit of sequential mutant populations

Consider a multitype birth–death process on types $1,2,3,\dots$ in which every type-$n$ cell independently divides at rate $\alpha_n$, dies at rate $\beta_n$, and at rate $\nu_n$ produces one type-$n$ and one type-$(n+1)$ cell. Start from one type-1 cell, assume $\lambda_1=\alpha_1-\beta_1>0$, and condition on the type-1 population never going extinct. Write $\lambda_n=\alpha_n-\beta_n$, the running-max fitness $\delta_n=\max_{1\le i\le n}\lambda_i$, and $r_n=\#\{i\le n:\lambda_i=\delta_n\}$. Let $Z_n(t)$ be the number of type-$n$ cells.

**Exact almost-sure limit.** For every $n$ there is a $(0,\infty)$-valued random variable $V_n$ with

$$\lim_{t\to\infty}t^{-(r_n-1)}e^{-\delta_nt}Z_n(t)=V_n\quad\text{a.s.}$$

$V_1$ is exponential with mean $\alpha_1/\lambda_1$. If $\delta_n>\lambda_{n+1}$ then $V_{n+1}=\nu_nV_n/(\delta_n-\lambda_{n+1})$ a.s., and if $\delta_n=\lambda_{n+1}$ then $V_{n+1}=\nu_nV_n/r_n$ a.s. In particular, if type 1 is the fittest of types $1,\dots,n$, every $V_i$, $i\le n$, is exponential.

**Small-mutation approximation.** In the limit of small mutation rates (taken in the order $\nu_1\to0,\dots,\nu_n\to0$) for an approximating model in which type-$(n+1)$ cells are seeded at rate $\nu_nV_nt^{r_n-1}e^{\delta_nt}$, $V_n$ is Mittag-Leffler distributed with tail parameter $\lambda_1/\delta_n\in(0,1]$ and scale $\omega_n$:

$$\mathbb E\,e^{-\theta V_n}=\big(1+(\omega_n\theta)^{\lambda_1/\delta_n}\big)^{-1},\qquad \omega_1=\alpha_1/\lambda_1,$$

$$\omega_{n+1}=\begin{cases}\dfrac{\nu_n}{\delta_n-\lambda_{n+1}}\,\omega_n,&\delta_n>\lambda_{n+1},\\[2mm] \dfrac{\nu_n}{r_n}\,\omega_n,&\delta_n=\lambda_{n+1},\\[2mm] \Big[c_n\,\nu_n\,\big(\log\nu_n^{-1}\big)^{r_n-1}\omega_n\Big]^{\lambda_{n+1}/\delta_n},&\delta_n<\lambda_{n+1},\end{cases}$$

with $c_n=\pi\,(\alpha_{n+1}/\lambda_{n+1})^{\delta_n/\lambda_{n+1}}\big/\big(\alpha_{n+1}\,\delta_n^{\,r_n-1}\sin(\pi\delta_n/\lambda_{n+1})\big)$. Thus $Z_n(t)\approx V_nt^{r_n-1}e^{\delta_nt}$ for large $t$, and $V_n$ has a power-law tail with exponent $\lambda_1/\delta_n$ (infinite mean) as soon as some type up to $n$ is fitter than type 1.

## Expansion

The key step is a lemma: if a deterministic source $f(t)\sim x\,t^re^{\delta t}$ seeds independent birth–death clones with net rate $\lambda$ at the points of a Poisson process of intensity $f$, the total clone size $Z(t)$ satisfies $t^{-r}e^{-\delta t}Z\to x/(\delta-\lambda)$ if $\delta>\lambda$, $t^{-r-1}e^{-\delta t}Z\to x/(r+1)$ if $\delta=\lambda$, and $e^{-\lambda t}Z\to V$ (random) if $\delta<\lambda$. Conditioning on the type-$n$ path and applying it inductively gives the almost-sure limits; when type $n+1$ is not fitter, the flux from type $n$ dominates and randomness is inherited unchanged. When type $n+1$ is fitter, the earliest mutants dominate and the limit is a sum over Poisson points with a power-law intensity, whose Laplace transform in the small-$\nu$ limit is the Mittag-Leffler form. The neutral factor $t^{r_n-1}$ comes from $\int_0^te^{\lambda s}e^{\lambda(t-s)}ds=te^{\lambda t}$.

## Sources

- M. D. Nicholson, D. Cheek, T. Antal, "Sequential mutations in exponentially growing populations", PLoS Computational Biology (2023), Model (Eq. (1) of the Model section); Results Eqs. (1)–(3); Methods, Proposition 1, Lemmas 1–2, Corollaries 1–2, Proposition 2 and Theorem 1, <https://doi.org/10.1371/journal.pcbi.1011289>, PMCID PMC10359018.
