# Haplotype block process and random coupon collection

**Setting.** In the Moran population of size $N$ started with $N$ distinct alleles, let $\hat T^{N,k}$ be the time at which the number of surviving alleles drops below $k$ and let the **haplotype block process** $\hat\pi^N_k$ be the vector of allele frequencies (a mass partition with at most $k-1$ coordinates) at time $\hat T^{N,k}$. Let $\mathcal{D}_k$ denote the random mass partition given by a Dirichlet random vector with parameter $(1,\dots,1)$ ($k$ entries), i.e. the uniform distribution on the simplex.

For a non-degenerate mass partition $m = (m_1,\dots,m_\ell)$ let $Y_1, Y_2, \dots$ be i.i.d. with law $m$, let $T = \inf\{n \ge 1 : \{Y_1,\dots,Y_n\} = \{1,\dots,\ell\}\}$ be the coupon-collector time, set $B^{(m)}_i = \sum_{k=1}^{T-1} \mathbf{1}_{Y_k = i}$ and $J^{(m)} = Y_T$ (the unique $i$ with $B^{(m)}_i = 0$). The vector $B^{(m)} = (B^{(m)}_i)_{i \ne J^{(m)}}$ is the **random coupon collection** associated with $m$.

**Theorem (haplotype block process).** As $N \to \infty$, $(\hat\pi^N_k)_{k\ge 2} \Rightarrow (\hat\pi^\infty_k)_{k \ge 2}$ in the sense of finite-dimensional distributions, where for every $K$ the chain $(\hat\pi^\infty_{K-i})_{i=0,\dots,K-2}$ is Markov with

1. initial law $\hat\pi^\infty_K \sim \mathcal{D}_{K-1}$;
2. transition: given $\hat\pi^\infty_{K-i}$, draw the random coupon collection $X_i = B^{(\hat\pi^\infty_{K-i})}$; given $X_i$, the next partition $\hat\pi^\infty_{K-(i+1)}$ is Dirichlet with parameter vector $X_i$.

**Contrast with the genealogy.** The ancestral block process $\pi^N_k$ (block frequencies of the $N$-Kingman coalescent at its jump times) converges to the Markov chain started from $\mathcal{D}_{K-1}$ in which, at each step, two blocks chosen uniformly among all pairs are merged (Kingman). Although the counting processes of alleles and of ancestral lineages coincide in law, the frequency vectors evolve by different Markov kernels: allele loss removes the coupon not yet collected and redistributes mass according to the collected counts.

## Depends on

- [Extinction process of alleles equals the Kingman block-counting process](extinction-process-equals-kingman-block-counting-process.md)

## Expansion

Between two consecutive allele extinctions, in the large-$N$ limit the allele frequencies follow a Wright–Fisher (Fleming–Viot) diffusion, whose embedded genealogy is a Pólya urn. Looking backward from the next extinction, each surviving allele's future share is determined by an urn started from the numbers of draws accumulated before the first time some colour has been drawn; that colour is the allele that goes extinct. Pólya urn limits are Dirichlet with parameter equal to the initial ball counts, which yields the coupon-collection transition. For general $\Lambda$-Fleming–Viot processes with no simultaneous extinctions the same description holds with the Dirichlet law replaced by the limit of a $\Lambda$-urn.

## Sources

- Guillaume Achaz, Amaury Lambert and Emmanuel Schertzer, "The sequential loss of allelic diversity", *Adv. Appl. Probab.* 50 (2018), 13-29. <https://doi.org/10.1017/apr.2018.67>
- Preprint version (the locators in this item follow its numbering): Guillaume Achaz, Amaury Lambert and Emmanuel Schertzer, "The sequential loss of allelic diversity", arXiv:1801.00683 (2018), Theorems 2.2 and 2.3 (binary case) and Section 3 (general $\Lambda$-Fleming–Viot case), <https://doi.org/10.48550/arXiv.1801.00683>.
