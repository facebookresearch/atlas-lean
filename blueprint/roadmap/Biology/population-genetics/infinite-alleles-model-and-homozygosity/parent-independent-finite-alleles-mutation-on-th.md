# Parent-independent finite-alleles mutation on the coalescent genealogy

Let $E=\{1,\ldots,K\}$ be a finite set of types, $K\ge1$, let $\pi=(\pi_1,\ldots,\pi_K)$ be a probability vector with $\pi_i>0$ for every $i$, and let $\theta>0$. Take a sample of $n\ge1$ genes whose genealogy is the [Kingman $n$-coalescent](../../coalescent-theory/partition-valued-kingman-coalescent/kingman-coalescent-on-n-as-a-time-indexed-cadlag.md) (each pair of lineages merges at rate $1$). Given the genealogy, mutations fall on every branch as a [Poisson point process](../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md) of rate $\theta/2$ per unit length, independently on distinct branches. At each mutation the gene takes a new type drawn from $\pi$, independently of everything else; the new type may equal the old one. The type of the most recent common ancestor is drawn from $\pi$, independently of the genealogy and of the mutations (stationary root). Types are inherited along branches between mutations. Then:

1. Two sampled genes are identical in state with probability

$$\mathbb P(\text{same type})=\sum_{i=1}^K\pi_i^2+\frac{1-\sum_{i=1}^K\pi_i^2}{1+\theta}.$$

2. For a sample of size $n$, the vector of type counts $(N_1,\ldots,N_K)$ has the Dirichlet-multinomial law with parameters $n$ and $\theta\pi=(\theta\pi_1,\ldots,\theta\pi_K)$:

$$\mathbb P(N_1=n_1,\ldots,N_K=n_K)=\frac{n!}{n_1!\cdots n_K!}\,\frac{\prod_{i=1}^K(\theta\pi_i)^{(n_i)}}{\theta^{(n)}},\qquad n_1+\cdots+n_K=n,$$

where $x^{(m)}=x(x+1)\cdots(x+m-1)$ is the rising factorial and $x^{(0)}=1$. Equivalently, the ordered sample types $(a_1,\ldots,a_n)\in E^n$ have the exchangeable law $\prod_i(\theta\pi_i)^{(n_i)}/\theta^{(n)}$, where $n_i$ is the number of $j$ with $a_j=i$.

Special cases. For the uniform law $\pi_i=1/K$, the identity probability is $\frac1K+\bigl(1-\frac1K\bigr)\frac1{1+\theta}$. As $\theta\downarrow0$ the identity probability tends to $1$; the case $\theta=0$ is excluded from the statement and enters only as this limit. Types with $\pi_i=0$ never occur and are removed from $E$ before the statement is applied; the Dirichlet-multinomial parameters must all be positive.

## Depends on

- [Kingman's coalescent on the natural numbers](../../coalescent-theory/partition-valued-kingman-coalescent/kingman-coalescent-on-n-as-a-time-indexed-cadlag.md)
- [Poisson point process with finite intensity](../../../Probability/point-processes/poisson-point-processes/poisson-point-process.md)

## Proof depends on

- [Kimura–Crow limit](tendsto-eq-homozygosity.md)
- [The Dirichlet law is stationary for parent-independent mutation](../diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md)

## Expansion

A full proof page must establish the following.

- Identity in state for $n=2$: trace the two lineages back. The first event is a coalescence with probability $1/(1+\theta)$, since the coalescence rate is $1$ and the total mutation rate is $2\cdot\theta/2$; then the genes are identical by descent. Otherwise the first event is a mutation, after which that gene's type is a fresh draw from $\pi$ independent of the other gene's type, which is itself $\pi$-distributed because the root type is $\pi$-distributed and parent-independent mutation preserves $\pi$. This gives $\frac1{1+\theta}+\frac\theta{1+\theta}\sum_i\pi_i^2$, which is the displayed formula.
- The $n$-sample law, by the coalescent with killing: trace lineages back, a lineage being killed at its first mutation and assigned an independent $\pi$-type, merging lineages at coalescences, and assigning the root type from $\pi$. The resulting Pólya-urn (Hoppe-type) construction gives the exchangeable sequence law and hence the Dirichlet-multinomial counts. Equivalently, the counts are the multinomial mixture over the [Dirichlet stationary law of parent-independent mutation](../diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/dirichlet-stationary-law-for-parent-independent.md); identifying the coalescent sample law with that mixture is a separate duality step and is not assumed here.
- The uniform-type corollary and the limit $\theta\downarrow0$.
- The role of the stationary root. If instead the root type is a fixed type $a$, the identity probability for $n=2$ changes in general. Conditioning on the coalescence time $T\sim\mathrm{Exp}(1)$ and writing $S=\sum_i\pi_i^2$, a direct computation gives

    $$S+\frac{1-S}{1+\theta}+\frac{2\theta\,(\pi_a-S)}{(1+\theta)(2+\theta)},$$

    which differs from item 1 whenever $\pi_a\ne S$; for the uniform law $\pi_a=S$ and the two agree. This probe is a local derivation, not a claim of the cited sources.
- Consistency with the infinite-alleles limit: letting $\max_i\pi_i\to0$ gives identity probability $1/(1+\theta)$, the value of the [Kimura–Crow limit](tendsto-eq-homozygosity.md).

## Sources

- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), <https://rd.springer.com/book/10.1007/978-0-387-78168-6>, finite-alleles model (statement and proof).
- A. Etheridge, *Some Mathematical Models from Population Genetics*, École d'Été de Probabilités de Saint-Flour XXXIX (2009), Lecture Notes in Mathematics 2012, Springer (2011), <https://link.springer.com/book/10.1007/978-3-642-16632-7>, duality (background).
