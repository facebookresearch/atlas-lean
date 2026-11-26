# The coalescence manifold stabilizes at n minus two population-size changes

**Setting.** Under the coalescent with effective population size $N(t)>0$ at time $t$ before the present (bounded above), pairs of lineages coalesce at rate $1/N(t)$ and mutations fall on the genealogy as a Poisson process. For a sample of $n$ genomes let $c_i=\mathbb E[T_{i,i}]$, $i=2,\dots,n$, be the expected time until the first coalescence among $i$ lineages; the expected site (allele) frequency spectrum is the image of $(c_2,\dots,c_n)$ under a fixed linear map depending only on $n$ (Polanski and Kimmel). With $R_N(t)=\int_0^t ds/N(s)$ and the transformed history $\tilde N(\tau)=N(R_N^{-1}(\tau))$,

$$c_i=\int_0^\infty\tilde N(\tau)\,e^{-\binom{i}{2}\tau}\,d\tau .$$

The *coalescence manifold* $\mathcal C_{n,k}$ is the closure of the normalized vectors $\mathbf c(N)/\|\mathbf c(N)\|_1$ over all piecewise-constant histories $N$ with at most $k$ breakpoints. Let $M_k(A)$ be the closure of moment vectors $(\int_0^1x^af(x)\,dx)_{a\in A}$ of nonnegative step functions with at most $k$ breakpoints.

**Theorem.**

1. With $A=\{\binom{i}{2}-1:i=2,\dots,n\}$,

$$\mathcal C_{n,k}=\Big\{\mathbf m\in M_k(A):\sum_{a\in A}m_a=1\Big\}.$$

2. $\mathcal C_{n,k}=\mathcal C_{n,n-2}$ for every $k\ge n-2$, and $\mathcal C_{n,n-3}\subsetneq\mathcal C_{n,n-2}$.
3. $\mathcal C_{n,n-2}$ is an affine slice of a projected spectrahedron, so the closest point of the manifold to an observed normalized spectrum is computable by semidefinite programming.

In words: every normalized expected frequency spectrum (equivalently coalescence vector) achievable by some piecewise-constant history from $n$ sampled genomes is achievable, up to closure, by a history with at most $n-2$ size changes, and $n-3$ changes do not suffice.

## Depends on

- [Piecewise-constant population-size history](../piecewise-history.md)
- [Expected time to the first coalescence](../first-coal-mean.md)
- [Expected SFS under a variable population size](../integral-sfs-of-indep.md)

## Proof depends on

- [Breakpoint bound for moments of nonnegative step functions](breakpoint-bound-for-moments-of-step-functions.md)

## Expansion

The time change $\tau=R_N(t)$ maps a step history to a step function $\tilde N$ with the same number of breakpoints, and the substitution $x=e^{-\tau}$ turns the Laplace-type integral into $\int_0^1\tilde N(-\log x)\,x^{\binom{i}{2}-1}\,dx$, a sparse moment of a step density on $[0,1]$. Item 1 then identifies the manifold with a normalized slice of the step-function moment cone. Since $|A|=n-1$, the breakpoint bound for step-function moments ($M_k(A)$ equals the full moment cone exactly when $k\ge|A|-1$) gives item 2. This halves the earlier stabilization bound $k=2n-2$ and shows the set of spectra reachable by complicated histories is already reached by histories with $n-2$ changes, which limits what a sample of $n$ genomes can reveal about population-size history.

## Sources

- Z. Rosen, G. Scholten, C. Vinzant, "Sparse moments of univariate step functions and allele frequency spectra", arXiv:2012.14467 (2020), Definitions 3.2 and 3.4, Theorem 3.5, Lemmas 3.6 and 3.7, Corollary 3.10, Section "Connections with semidefinite programming", <https://doi.org/10.48550/arXiv.2012.14467>; published in *Vietnam Journal of Mathematics* 50(2) (2022) 523–544, <https://doi.org/10.1007/s10013-022-00548-5>. Locators follow arXiv v1.
