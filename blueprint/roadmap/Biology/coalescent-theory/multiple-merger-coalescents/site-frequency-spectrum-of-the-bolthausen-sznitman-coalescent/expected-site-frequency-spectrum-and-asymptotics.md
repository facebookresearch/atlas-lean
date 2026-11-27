# Site frequency spectrum of the Bolthausen–Sznitman coalescent

**Setting.** The Bolthausen–Sznitman coalescent is the $\Lambda$-coalescent with $\Lambda$ uniform on $[0,1]$: when there are $m$ blocks, each particular group of $k\ge2$ of them merges at rate $\lambda_{m,k}=\frac{(k-2)!(m-k)!}{(m-1)!}$. It arises as the genealogy of populations under rapid selection, such as pathogens and tumors, and of Derrida-type random-energy models. For a sample of size $n$, let $\ell_{n,b}$ be the total length of the branches that support exactly $b$ of the $n$ leaves. Under the infinite-sites model with mutations at rate $\theta$ along branches, $SFS_{n,b}$ (the number of mutations carried by exactly $b$ individuals) is mixed Poisson with mean $\theta\,\ell_{n,b}$ given the tree. Set

$$L_1(n,b)=\int_0^1\frac{\Gamma(b-p)}{\Gamma(b+1)}\,\frac{\Gamma(n-b+p)}{\Gamma(n-b+1)}\,\frac{dp}{\Gamma(1-p)\Gamma(1+p)} .$$

**Theorem.**

1. (Exact moments) For $1\le b\le n-1$, $\mathbb E[\ell_{n,b}]=nL_1(n,b)$ and $\mathbb E[SFS_{n,b}]=\theta nL_1(n,b)$. Second moments $\mathbb E[\ell_{n,b_1}\ell_{n,b_2}]$, and hence $\operatorname{Cov}(SFS_{n,b_1},SFS_{n,b_2})$, are given by explicit one- and two-dimensional integrals $L_2,L_3$ of the same type, with $L_3$ contributing only when $b_1+b_2\le n$.
2. (Asymptotic spectrum) As $n\to\infty$:
   - singletons: $\dfrac{\log n}{n}\,\mathbb E[SFS_{n,1}]\to\theta$;
   - if $b\ge2$ and $b/n\to0$: $\dfrac{b(b-1)}{n}\log^2\!\Big(\dfrac nb\Big)\,\mathbb E[SFS_{n,b}]\to\theta$;
   - if $b/n\to u\in(0,1)$: $n\,\mathbb E[SFS_{n,b}]\to\theta f_1(u)$, where $f_1(u)=\displaystyle\int_0^1u^{-1-p}(1-u)^{p-1}\frac{\sin\pi p}{\pi p}\,dp$.
3. (Infinite-population frequency spectrum) For $I\subset(0,1)$, the expected total length of branches whose asymptotic frequency lies in $I$ is $\int_If_1(u)\,du$, so $\mathbb E[SFS_I]=\theta\int_If_1(u)\,du$.
4. (Law of large numbers) If $b=o(\sqrt n/\log n)$, then $SFS_{n,b}/\mathbb E[SFS_{n,b}]\to1$ in $L^2$.
5. (High-frequency classes) For $n/2<b<n$ the law of $\ell_{n,b}$ is explicit. If $b/n\to u\in[\tfrac12,1)$ and $\alpha=\log\frac{1-u}{u}$, then

$$\frac n{\log n}\,\mathbb P(\ell_{n,b}>0)\to\frac{G(\alpha)}{u(1-u)},\qquad G(x)=\frac{1+e^x}{\pi^2+x^2},$$

and conditionally on $\ell_{n,b}>0$, $(\log n)\ell_{n,b}$ has the limiting tail $G(\alpha-s)/G(\alpha)$.

## Depends on

- [Infinite-sites mutation on a finite genealogy](../../poisson-mutation-on-the-kingman-genealogy/branch-mutation-kernel.md)
- [Merger rates of the Bolthausen–Sznitman coalescent](../../coalescents/merger-rate-volume.md)

## Proof depends on

## Expansion

The computations use the random recursive tree (cutting-merge) construction of the Bolthausen–Sznitman coalescent, equivalently its embedding in a continuous-state branching process (Neveu's), where block sizes evolve through Gamma-function ratios. The integral over $p\in(0,1)$ with weight $\sin(\pi p)/(\pi p)$ comes from Euler's reflection formula, which gives $1/(\Gamma(1-p)\Gamma(1+p))=\sin(\pi p)/(\pi p)$. Compared with Kingman's $\mathbb E[SFS_{n,b}]=2\theta/b$ (pair coalescence rate $1$, mutation rate $\theta$ along branches), the spectrum here is U-shaped. Singletons are inflated by the $n/\log n$ external length, and intermediate classes decay like $1/(b^2\log^2(n/b))$. High-frequency variants reflect single large merger events and occur with probability of order $\log n/n$. These are the signatures used to distinguish selection-driven multiple-merger genealogies from neutral Kingman genealogies in data.

## Sources

- Götz Kersting, Arno Siri-Jégousse, Alejandro H. Wences, "Site Frequency Spectrum of the Bolthausen-Sznitman Coalescent", arXiv:1910.01732 (2019), Theorem 2.1, Corollary 2.2, Theorem 3.1, Corollary 3.2, Theorems 3.4–3.5, Corollary 3.6 (whose limit $\theta$ is a misprint for $1$, since the ratio has mean $1$), Theorem 4.1 and Corollary 4.2, <https://doi.org/10.48550/arXiv.1910.01732>; published in *ALEA Latin American Journal of Probability and Mathematical Statistics* 18 (2021), <https://doi.org/10.30757/alea.v18-53>. Locators follow arXiv v1.
