# Collapsed site frequency spectrum across polyploid subgenomes

Let $\phi(x_1,\dots,x_S)$ be the density of derived-allele frequencies in the $S$ subgenomes of a polyploid with ploidies $k_1,\dots,k_S$, for example the solution of the [subgenome diffusion](polyploid-subgenome-diffusion-with-homoeologous-exchange.md). For a sample of $n$ individuals, subgenome $i$ contributes $nk_i$ chromosomes. The expected multidimensional frequency spectrum is

$$\mathbb E[d_1,\dots,d_S]=\int_{[0,1]^S}\prod_{i=1}^S\binom{nk_i}{d_i}x_i^{d_i}(1-x_i)^{nk_i-d_i}\,\phi(x_1,\dots,x_S)\,dx_1\cdots dx_S .$$

When two subgenomes cannot be separated bioinformatically, the spectrum is **collapsed** along them:

$$\mathbb E_{\mathrm{comb}}[d]=\sum_{d_1=0}^{nk_1}\mathbb E[d_1,\,d-d_1],\qquad d=0,1,\dots,nk_1+nk_2,$$

with $\mathbb E[d_1,d_2]=0$ outside $0\le d_2\le nk_2$. Collapsing several subgenomes iterates this. Then:

1. **Convolution form.** $\mathbb E_{\mathrm{comb}}[d]=\int\Pr\big[\mathrm{Bin}(nk_1,x_1)+\mathrm{Bin}(nk_2,x_2)=d\big]\,\phi\,dx_1\,dx_2$ with independent binomials, so the collapsed spectrum is the expected spectrum of the total derived count among the $n(k_1+k_2)$ chromosomes. The total mass is preserved.
2. **Mixed subgenomes.** If $\phi$ is concentrated on the diagonal $x_1=x_2=x$ with marginal density $\varphi(x)$, then $\mathbb E_{\mathrm{comb}}[d]=\int\binom{n(k_1+k_2)}{d}x^d(1-x)^{n(k_1+k_2)-d}\varphi(x)\,dx$. This is the one-population spectrum with sample size $n(k_1+k_2)$; an autotetraploid with free exchange looks like a diploid with twice the sample size.
3. **Fixed differences.** A site fixed for opposite alleles in the two subgenomes ($x_1=1$, $x_2=0$) contributes only to $d=nk_1$. For equal ploidies this is the midpoint $d=n(k_1+k_2)/2$, the source of the excess of 50% sites in collapsed spectra of allopolyploids. Homoeologous exchange spreads this peak and removes it as $E_{i\leftrightarrow j}$ grows.

## Depends on

- [Subgenome diffusion for a polyploid with homoeologous exchange](polyploid-subgenome-diffusion-with-homoeologous-exchange.md)
- [Expected site frequency spectrum under the Poisson random field](../diffusion-theory/poisson-random-field-model/expected-sfs.md)

## Proof depends on

- [Vandermonde's identity](../../../Combinatorics/binomial-coefficients/binomial-sums/vandermonde-identity.md)
- [Expected site frequency spectrum under the Poisson random field](../diffusion-theory/poisson-random-field-model/expected-sfs.md)

## Expansion

Item 1 is the definition of the collapse together with the independence of binomial sampling within subgenomes given $(x_1,x_2)$: summing the product of two binomial probabilities over $d_1+d_2=d$ is the law of their sum. Item 2 is Vandermonde's identity, $\sum_{d_1}\binom{a}{d_1}\binom{b}{d-d_1}=\binom{a+b}{d}$, applied with a common success probability $x$. Item 3 is direct substitution. Collapsing loses identifiability: in simulations, parameters of the polyploid's own history (bottleneck size, formation time, exchange rate) were estimated precisely from the one-dimensional collapsed spectrum, but parental population sizes before formation were unstable or unbounded.

## Sources

- P. D. Blischak, M. Sajan, M. S. Barker and R. N. Gutenkunst, "Demographic history inference and the polyploid continuum", Genetics 224(4) (2023), iyad107, <https://doi.org/10.1093/genetics/iyad107>, PMCID PMC10411560. Equations (3) and (4), section "Combining polyploid subgenomes", Fig. 2 (collapse), Figs. 3-4 (50% spike and its erosion by exchange), Fig. 5 and the discussion of parameter identifiability. Items 1-3 are derived above from Equations (3)-(4).
