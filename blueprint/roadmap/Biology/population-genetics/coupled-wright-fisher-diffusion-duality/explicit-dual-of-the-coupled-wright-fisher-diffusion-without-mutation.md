# Explicit dual of the coupled Wright–Fisher diffusion without mutation

**Setting.** Let $X$ be the coupled Wright–Fisher diffusion on $L$ loci with single-locus selection $h$ and pairwise interactions $J$, and with no mutation ($\theta_l=0$ for all $l$). The boundaries are then absorbing, and no stationary law charges only the interior, so the moment function $k$ of the general dual is unavailable. Use instead the multivariate Beta function

$$k(n)=\prod_{l=1}^LB(n^{(l)}),\qquad B(n^{(l)})=\frac{\prod_{i=1}^{M_l}\Gamma(n^{(l)}_i)}{\Gamma(n^{(l)})},\qquad n^{(l)}=\sum_in^{(l)}_i,$$

and the duality function $F(x,n)=\prod_l B(n^{(l)})^{-1}\prod_i(x^{(l)}_i)^{n^{(l)}_i}$.

**Corollary.** There is a pure-jump Markov dual $N$ on $\mathbb N^M$, with respect to $F$, whose rates are fully explicit:

$$q(n,n-e^{(l)}_i)=\frac{n^{(l)}_i\,(n^{(l)}-1)}2,$$

$$q(n,n+e^{(l)}_j)=n^{(l)}_j\sum_{k\ne j}h^{(l)}_k+\frac{n^{(l)}_j}{n^{(l)}}\sum_{r\ne l}\sum_{i=1}^{M_r}n^{(r)}_iJ^{(lr)}_{ji},$$

$$q(n,n+e^{(l)}_j+e^{(r)}_h)=(n^{(l)}+n^{(r)})\,\frac{n^{(l)}_jn^{(r)}_h}{n^{(l)}n^{(r)}}\sum_{k\ne j}\sum_{m\ne h}J^{(lr)}_{km}\qquad(r>l).$$

Consequently, the moments of the allele frequencies satisfy

$$\mathbb E\Bigl[\prod_{l,i}X^{(l)}_i(t)^{n^{(l)}_i}\Bigm|X(0)=x\Bigr]=\mathbb E\Bigl[\prod_l\frac{B(n^{(l)})}{B(N^{(l)}(t))}\prod_{l,i}\bigl(x^{(l)}_i\bigr)^{N^{(l)}_i(t)}\Bigm|N(0)=n\Bigr].$$

Letting $t\to\infty$ links fixation and extinction probabilities of allele types to the long-run behaviour of $N$.

## Depends on

- [Coupled ancestral selection graphs as the dual of the coupled Wright–Fisher diffusion](coupled-ancestral-selection-graphs-as-the-dual-of-the-coupled-wright-fisher-diffusion.md)

## Expansion

In the neutral one-locus model with parent-independent mutation, $k(n)=B(n+2u)/B(2u)$, which tends to $B(n)$ as $\theta\to0$. This motivates the choice of $k$. With this $k$, every ratio $k(\hat n)/k(n)$ in the general rates is a ratio of Gamma functions, e.g. $B(n-e_i)/B(n)=(n^{(l)}-1)/(n^{(l)}_i-1)$ and $B(n+e_j)/B(n)=n^{(l)}_j/n^{(l)}$. Substituting these turns the implicit rates of the mutation-driven dual into the closed forms above. Since there is no mutation, the mutation jumps disappear, and the same generator calculation and duality criterion give the process duality.

## Sources

- M. Favero, H. Hult, T. Koski, "A dual process for the coupled Wright–Fisher diffusion", *Journal of Mathematical Biology* 82(1):6 (2021), Section 5, Eq. (23), Corollary 1, Eq. (24), Section 6, <https://doi.org/10.1007/s00285-021-01555-9>, PMCID PMC7822808.
