# Coupled ancestral selection graphs as the dual of the coupled Wright–Fisher diffusion

**Setting.** Let $X$ be the coupled Wright–Fisher diffusion on $L$ loci with single-locus selection $h$, pairwise interactions $J$ and mutation rates $u^{(l)}_{ij}$. Assume that it has a stationary law $\tilde X$ with $P(\tilde X^{(l)}_i=0)=0$ for all $i,l$. For $n\in\mathbb N^M$, with $n^{(l)}=\sum_in^{(l)}_i$ and unit vectors $e^{(l)}_i$, define

$$k(n)=\mathbb E\prod_{l,i}\bigl(\tilde X^{(l)}_i\bigr)^{n^{(l)}_i},\qquad F(x,n)=\frac1{k(n)}\prod_{l=1}^L\prod_{i=1}^{M_l}\bigl(x^{(l)}_i\bigr)^{n^{(l)}_i}.$$

**Theorem.** There is a pure-jump Markov process $N$ on $\mathbb N^M$ such that

$$\mathbb E\bigl[F(X(t),n)\mid X(0)=x\bigr]=\mathbb E\bigl[F(x,N(t))\mid N(0)=n\bigr].$$

From $n\neq0$, $N$ jumps to:

- **coalescence** $n-e^{(l)}_i$ (if $n^{(l)}_i\ge2$), at rate $\dfrac{n^{(l)}_i(n^{(l)}_i-1)}2\dfrac{k(n-e^{(l)}_i)}{k(n)}$;
- **mutation** $n-e^{(l)}_i+e^{(l)}_j$ ($i\ne j$, $n^{(l)}_i\ge1$), at rate $n^{(l)}_iu^{(l)}_{ji}\dfrac{k(n-e^{(l)}_i+e^{(l)}_j)}{k(n)}$;
- **single branching** $n+e^{(l)}_j$, at rate $\Bigl(n^{(l)}\sum_{k\ne j}h^{(l)}_k+\sum_{r\ne l}\sum_in^{(r)}_iJ^{(lr)}_{ji}\Bigr)\dfrac{k(n+e^{(l)}_j)}{k(n)}$;
- **double branching** $n+e^{(l)}_j+e^{(r)}_h$ ($r>l$), at rate $(n^{(l)}+n^{(r)})\sum_{k\ne j}\sum_{m\ne h}J^{(lr)}_{km}\dfrac{k(n+e^{(l)}_j+e^{(r)}_h)}{k(n)}$.

The diagonal rate $q(n,n)$ makes each row sum to zero. $N$ is the block-counting process of $L$ coupled ancestral selection graphs. Coalescence, mutation and single branching act on one locus at a time, while double branching, caused by pairwise selection, adds lineages at two loci simultaneously. If $J=0$, double branching vanishes and $N$ splits into $L$ independent ancestral selection graphs.

## Depends on

- [Coupled Wright–Fisher diffusion with pairwise selection](coupled-wright-fisher-diffusion-with-pairwise-selection.md)
- [Generator of the ancestral selection graph line-counting process](../selection-duality-and-general-one-dimensional-di/asg-generator.md)

## Expansion

The proof is a generator computation. Apply $\mathcal L$ to $F(\cdot,n)$ and use identities such as $x_i^{-1}F(x,n)=\frac{k(n-e_i)}{k(n)}F(x,n-e_i)$ and $x_iF(x,n)=\frac{k(n+e_i)}{k(n)}F(x,n+e_i)$, together with $x_i=1-\sum_{j\ne i}x_j$, which makes the selection coefficients positive. This rewrites $\mathcal LF(\cdot,n)(x)$ as $\sum_{\hat n}q(n,\hat n)F(x,\hat n)+q(n,n)F(x,n)$ with $q(n,\hat n)\ge0$. Taking stationary expectations, $\mathbb E\,\mathcal LF(\tilde X,n)=0$ and $\mathbb EF(\tilde X,\cdot)\equiv1$, so the rows sum to zero and the coefficients form a rate matrix $Q$ with $\mathcal LF(\cdot,n)(x)=\mathcal L_DF(x,\cdot)(n)$. Generator duality becomes process duality by the Ethier–Kurtz duality criterion, whose moment conditions are verified in Section 6. The total lineage count $\|N\|_1$ moves by $+2$, $+1$ or $-1$, with branching rates at most linear and coalescence rates at least quadratic in $\|N\|_1$, so a simpler birth–death chain dominates its jump chain (Appendix). For one biallelic locus this is the line-counting process of the ancestral selection graph with types and mutations included backward in time.

## Sources

- M. Favero, H. Hult, T. Koski, "A dual process for the coupled Wright–Fisher diffusion", *Journal of Mathematical Biology* 82(1):6 (2021), Section 3 (Eqs. 3, 11–18), Section 4 (Eqs. 19–22), Theorem 1, Section 6 (proof of Theorem 1), <https://doi.org/10.1007/s00285-021-01555-9>, PMCID PMC7822808.
