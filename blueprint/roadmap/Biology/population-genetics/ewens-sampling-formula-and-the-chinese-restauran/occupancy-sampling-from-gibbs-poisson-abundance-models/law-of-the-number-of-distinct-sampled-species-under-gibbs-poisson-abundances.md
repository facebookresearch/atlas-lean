# Law of the number of distinct sampled species under Gibbs–Poisson abundances

**Model.** Fix nonnegative weights $\phi_m$ ($m\ge1$, $\phi_1>0$), $\phi(x)=\sum_{m\ge1}\phi_mx^m/m!$ with radius of convergence $x_0>0$, and $\theta>0$. The partition function $Z_\theta(x)=e^{\theta\phi(x)}=1+\sum_{k\ge1}\sigma_k(\theta)x^k/k!$ defines the Bell polynomials $\sigma_k(\theta)=\sum_{l=1}^kB_{k,l}(\phi_\bullet)\theta^l$. A **Gibbs–Poisson** (compound Poisson) abundance $\xi$ has $\mathbb{P}(\xi=k)\propto\sigma_k(\theta)x^k/k!$ for some $x\in(0,x_0)$. A population has $n$ species with i.i.d. abundances $\xi_1,\dots,\xi_n$, and a $k$-sample is the occupancy vector $(\xi_1,\dots,\xi_n)$ conditioned on $\sum_i\xi_i=k$ (Kolchin's generalized allocation scheme). Let $P_{n,k}$ be the number of distinct species in the sample. The negative binomial abundance, $\sigma_k(\theta)=\theta(\theta+1)\cdots(\theta+k-1)$, gives the Ewens–Dirichlet model.

**Proposition.** The law of the sample does not depend on the tilt $x$, and the conditional (microcanonical) law of the occupancies given $P_{n,k}$ does not depend on $n$, so $P_{n,k}$ is a sufficient statistic for $n$ when $\theta$ is known. Moreover

$$\mathbb{E}\big[u^{P_{n,k}}\big]=\sum_{p=0}^{n-1}\binom{n}{p}u^{n-p}(1-u)^p\,\frac{\sigma_k\big((n-p)\theta\big)}{\sigma_k(n\theta)},\qquad
\mathbb{P}(P_{n,k}=p)=\binom{n}{p}\sum_{q=1}^{p}(-1)^{p-q}\binom{p}{q}\frac{\sigma_k(q\theta)}{\sigma_k(n\theta)},$$

for $p\in\{1,\dots,n\wedge k\}$. In particular

$$\mathbb{E}[P_{n,k}]=n\Big(1-\frac{\sigma_k((n-1)\theta)}{\sigma_k(n\theta)}\Big),\qquad \mathrm{Var}(P_{n,k})=n\Big(\frac{\sigma_k((n-1)\theta)}{\sigma_k(n\theta)}+(n-1)\frac{\sigma_k((n-2)\theta)}{\sigma_k(n\theta)}-n\Big(\frac{\sigma_k((n-1)\theta)}{\sigma_k(n\theta)}\Big)^2\Big).$$

Equivalently $\mathbb{P}(P_{n,k}=p)=\dfrac{n!}{(n-p)!}\,\dfrac{B_{k,p}(\sigma_\bullet(\theta))}{\sigma_k(n\theta)}$ with $B_{k,p}(\sigma_\bullet(\theta))=\sum_{l=p}^{k}B_{k,l}(\phi_\bullet)S_{l,p}\theta^l$, where $S_{l,p}$ are Stirling numbers of the second kind.

**Infinitely many species.** Letting $n\to\infty$ and $\theta\to0$ with $n\theta\to\gamma>0$ gives well-defined sampling formulae for a population with infinitely many species, in which $\gamma$ is the species-richness (diversity) parameter; for negative binomial abundances these are the Ewens sampling formulae.

## Depends on

- [Ewens sampling formula](../ewens-prob.md)

## Proof depends on

## Expansion

Conditioning i.i.d. compound Poisson counts on their sum makes the exponential tilt $x^k$ cancel, so the sample law is $\prod_i\sigma_{k_i}(\theta)/k_i!$ normalized by $\sigma_k(n\theta)/k!$, using $Z_\theta^n=Z_{n\theta}$. Choosing which $p$ species are seen and expanding $(1-u+uZ_\theta(x))^n$ by the binomial theorem gives the probability generating function, and inclusion–exclusion over the set of seen species gives the alternating sum. Since the law of $P_{n,k}$ depends on $n$ only through these ratios, $n$ can be estimated from the observed $P_{n,k}$ by maximum likelihood or moments.

## Sources

- Thierry Huillet and Servet Martinez, "Occupancy distributions arising in sampling from Gibbs-Poisson abundance models", arXiv:1307.3000 (2013), Section 2 (partition function and allocation scheme), Proposition 1 and the following corollary, and the infinitely-many-species limit in Section 2, <https://doi.org/10.48550/arXiv.1307.3000>; published in *Journal of Statistical Physics* 153(5) (2013) 763–800, <https://doi.org/10.1007/s10955-013-0865-y>. Locators follow arXiv v2.
