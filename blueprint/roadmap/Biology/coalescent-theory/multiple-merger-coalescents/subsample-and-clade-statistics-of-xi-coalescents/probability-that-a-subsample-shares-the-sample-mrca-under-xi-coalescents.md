# Probability that a subsample shares the sample MRCA under Ξ-coalescents

**Setting.** Let $\Pi^{(n)}$ be a $\Xi$-$n$-coalescent (an exchangeable coalescent with simultaneous multiple mergers) started from the sample $[n]=\{1,\dots,n\}$, and fix a subsample $[m]$, $2\le m<n$. Let $p^{(\Xi)}_{n,m}$ be the probability that the most recent common ancestor (MRCA) of the subsample equals the MRCA of the whole sample, i.e. that the root of the genealogy of $[m]$ is the root of the genealogy of $[n]$. Let $B^{(n)}_{[1]}\ge B^{(n)}_{[2]}\ge\cdots$ be the sizes of the blocks that are merged at the final collision (absorption), padded with zeros.

**Theorem.**
1. For every $\Xi$-$n$-coalescent,

$$p^{(\Xi)}_{n,m}=1-\mathbb E\Big(\sum_{i\ge1}\prod_{k=0}^{m-1}\frac{B^{(n)}_{[i]}-k}{n-k}\Big)>0 .$$

2. The limit $p^{(\Xi)}_m=\lim_{n\to\infty}p^{(\Xi)}_{n,m}$ exists, and it is positive if and only if the $\Xi$-coalescent does not stay infinite. If the coalescent comes down from infinity, then

$$p^{(\Xi)}_{n,m}\longrightarrow 1-\mathbb E\Big(\sum_{i\ge1}P_{[i]}^m\Big)=1-\mathbb E\big(X^{m-1}\big)=1-\frac{\mathbb E(Y^m)}{\mathbb E(Y)},$$

where $P_{[i]}=\lim_n B^{(n)}_{[i]}/n$ are the asymptotic frequencies of the $K$ blocks merging at absorption, $X$ is the frequency of a size-biased pick among them, $\mathbb P(X\in\cdot)=\mathbb E\sum_iP_{[i]}\delta_{P_{[i]}}(\cdot)$, and $Y$ has the mean empirical law of the merging frequencies, $\mathbb P(Y\in\cdot)=\mathbb E\sum_i\delta_{P_{[i]}}(\cdot)/\mathbb E K$. The identity $\mathbb E(X^{m-1})=\mathbb E(Y^m)/\mathbb E(Y)$ is for this $Y$; it fails for a uniform pick among the $K$ blocks given a random $K$.
3. (Bolthausen–Sznitman coalescent, $\Lambda=\mathrm{Beta}(1,1)$) With $B_1,\dots,B_{n-1}$ independent Bernoulli variables, $\mathbb P(B_i=1)=1/i$,

$$p^{(\mathrm{Beta}(1,1))}_{n,m}=\mathbb E\Big(\frac{B_1+\cdots+B_{m-1}}{B_1+\cdots+B_{n-1}}\Big),\qquad \log(n)\,p^{(\mathrm{Beta}(1,1))}_{n,m}\to\sum_{i=1}^{m-1}\frac1i\quad(n\to\infty).$$

So under the Bolthausen–Sznitman coalescent, which stays infinite, a fixed subsample almost never reaches the sample MRCA in large samples; Kingman's coalescent is the classical case with a positive limit, but it does not maximize $p^{(\Xi)}_{n,m}$ (nearly star-shaped coalescents do better).

## Expansion

The subsample misses the sample root exactly when all of $[m]$ has coalesced into one block before the last collision, i.e. $[m]\subseteq B^{(n)}_{[i]}$ for some block merged at absorption. By exchangeability, given the block sizes this has probability $\sum_i\prod_{k<m}(B^{(n)}_{[i]}-k)/(n-k)$, which gives part 1; letting $n\to\infty$ and using Kingman's paintbox representation of the exchangeable partition before absorption gives part 2. For $\Lambda$-coalescents a first-jump recursion over the number of subsample blocks among the merged ones computes $p^{(\Lambda)}_{n,m}$ exactly. The Bernoulli representation for the Bolthausen–Sznitman case comes from its random-recursive-tree (cutting) construction. This quantifies how much ancestral information a subsample carries about the whole sample.

## Depends on

- [Kingman case: MRCA of a subsample equals the sample MRCA](../../ranked-labeled-histories-of-coalescent-trees/mrca-of-a-subsample-equals-sample-mrca-with-prob.md)
- [The Ξ-coalescent rate matrix on partitions of a finite sample](../../coalescents/xi-coalescent-partition-valued-ctmc-and-restrict.md)
- [Merger rates of the Bolthausen–Sznitman coalescent](../../coalescents/merger-rate-volume.md)

## Proof depends on

- [Exponential edge lifting constructs the finite Bolthausen–Sznitman coalescent](../merger-rates-and-beta-coalescents/lifting-the-edges-of-a-random-recursive-tree-at.md)

## Sources

- Fabian Freund, "Multiple-merger genealogies: models, consequences, inference", in *Probabilistic Structures in Evolution* (E. Baake and A. Wakolbinger, eds.), EMS Series of Congress Reports, EMS Press (2021), 179–202, <https://doi.org/10.4171/ECR/17-1/9>; preprint arXiv:2010.12271 (2020), section "How much genetic information is contained in a subsample?", recursion for $p^{(\Lambda)}_{n,m}$ and its two propositions (after Eldon and Freund, Props. 2, 4 and 5), <https://doi.org/10.48550/arXiv.2010.12271>.
- Bjarki Eldon and Fabian Freund, "Genealogical properties of subsamples in highly fecund populations", *Journal of Statistical Physics* 172 (2018), 175–207, <https://doi.org/10.1007/s10955-018-2013-1> (original proofs).
