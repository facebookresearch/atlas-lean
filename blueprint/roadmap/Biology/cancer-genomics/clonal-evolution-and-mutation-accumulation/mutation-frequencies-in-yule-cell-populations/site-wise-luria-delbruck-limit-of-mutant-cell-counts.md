# Site-wise Luria–Delbrück limit of mutant cell counts

**Model.** Start with one cell; cells divide independently at rate $1$ (Yule process). Genomes are elements of $\mathcal{G}=\mathcal{N}^{\mathcal{S}}$ with nucleotides $\mathcal{N}=\{A,C,G,T\}$ and a finite site set $\mathcal{S}$. At each division, independently over sites $i\in\mathcal{S}$ and over the two daughters, the daughter's nucleotide at site $i$ equals the parent's with probability $1-\mu$ and equals each of the three other nucleotides with probability $\mu/3$. Let $\sigma_n$ be the first time the population has $n$ cells, and let $B_i^{n,\mu}$ be the number of cells alive at $\sigma_n$ whose nucleotide at site $i$ differs from the initial cell's.

The **Luria–Delbrück distribution with parameter $c$** is the law of $B=\sum_{k=1}^{K}Y_k$, with $K\sim\mathrm{Poisson}(c)$ independent of i.i.d. $Y_k$ satisfying $\mathbb{P}[Y_k=j]=1/(j(j+1))$, $j\ge1$; equivalently $\mathbb{E}z^B=(1-z)^{c(z^{-1}-1)}$. Its tail satisfies $m\,\mathbb{P}[B\ge m]\to c$.

**Theorem.** As $n\to\infty$ with $n\mu\to\theta\in[0,\infty)$:

1. $(B_i^{n,\mu})_{i\in\mathcal{S}}\to(B_i)_{i\in\mathcal{S}}$ in distribution, where the $B_i$ are i.i.d. Luria–Delbrück with parameter $2\theta$.
2. If in addition $|\mathcal{S}|\to\infty$, the empirical distribution $\frac{1}{|\mathcal{S}|}\sum_{i\in\mathcal{S}}\delta_{B_i^{n,\mu}}$ converges in probability, in the weak topology on probability measures on $\{0,1,2,\dots\}$, to the Luria–Delbrück distribution with parameter $2\theta$.

So different sites are asymptotically independent, and the across-genome histogram of mutant counts estimates the per-site law.

## Depends on

- [Luria–Delbrück distribution](../../../population-genetics/luria-delbr-ck-distribution/ld-pmf.md)

## Expansion

Mutations at a site arise at rate proportional to the number of divisions, i.e. about $2\mu$ per cell, so over the growth to $n$ cells the number of mutation events that leave descendants of bounded size is Poisson with mean $\approx 2n\mu$. A mutation arising when the population has size $k$ founds a clone whose final size is (in the limit) geometric with a uniformly distributed parameter, which yields the $1/(j(j+1))$ clone-size law. Double mutations at one site and back mutations are negligible because $\mu\to0$. Asymptotic independence across sites holds because only $O(n^{3/2})$ divisions occur before $\sigma_n$ along the relevant embedded chain and simultaneous mutation at two given sites in one division has probability $O(\mu^2)$. The law of large numbers follows from pairwise asymptotic independence.

## Sources

- D. Cheek, T. Antal, "Genetic composition of an exponentially growing cell population", arXiv:1905.12355 (2019), Section 2 (model), Section 3.1 (Lemma 3.1), Theorems 4.1 and 4.3, <https://doi.org/10.48550/arXiv.1905.12355>.
