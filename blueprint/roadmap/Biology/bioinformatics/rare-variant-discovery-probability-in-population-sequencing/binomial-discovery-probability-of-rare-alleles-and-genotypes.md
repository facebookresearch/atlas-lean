# Binomial discovery probability of rare alleles and genotypes

**Setting.** A rare variant has population frequency $\phi$ (minor allele frequency, or rare homozygous genotype frequency). Each of $\sigma$ independently sampled diploid genomes is sequenced separately to the same haploid redundancy $\rho$, so the project-wide redundancy is $R=\sigma\rho$. Let $c=c(\rho,\tau)$ be the probability that the variant's position on a given chromosome is spanned by at least $\tau$ reads (the read-covering threshold used to control sequencing error), the same for both chromosomes, independent across the two chromosomes, and independent of the variant's presence. The variant is *discovered* if it is detected in at least $N$ samples.

**Theorem 1 (rare alleles).** Let $A_j$ be the event that chromosome $j\in\{1,2\}$ of a sample carries the allele, with $\Pr[A_j]=\phi$ independently, and $C_j$ the event that its position on chromosome $j$ is covered at least $\tau$ times. The detection event $D_A=(A_1\cap C_1)\cup(A_2\cap C_2)$ has

$$\Pr[D_A]=2\phi c-\phi^2c^2.$$

With $K$ the number of samples in which the variant is detected, $K\sim\mathrm{Binomial}(\sigma,\Pr[D_A])$ and the discovery probability is

$$P_v=\Pr[K\ge N]=\sum_{k=N}^{\sigma}\binom{\sigma}{k}\Pr[D_A]^k\bigl(1-\Pr[D_A]\bigr)^{\sigma-k}.$$

**Theorem 2 (rare genotypes).** A rare genotype $G$ (frequency $\phi$) is detected only if both chromosomes are covered, $D_G=G\cap C_1\cap C_2$, so $\Pr[D_G]=\phi c^2$, and its discovery probability is the same binomial tail with $\Pr[D_G]$ in place of $\Pr[D_A]$.

**Design consequence.** For fixed total redundancy $R$, substituting $\rho=R/\sigma$ makes $P_v$ a function of the sample size $\sigma$ alone; the source shows (Theorem 3) that for $N=1$ and $N=2$ it has a single interior maximizer $\sigma^*$, necessarily a global maximum, except for rare alleles with $\tau = 1$, where $P_v(\sigma)$ increases monotonically to its supremum as $\sigma \to \infty$ (Wendl and Wilson 2009, Eq. (10)); its numerical study shows that $\sigma^*$ increases with $R$ and that $P_v$ falls off faster for $\sigma<\sigma^*$ than for $\sigma>\sigma^*$, so fixing the sample size in advance of the sequencing budget is generally suboptimal.

## Expansion

$\Pr[A_j\cap C_j]=\phi c$ by independence of the allele and the coverage process, and $\Pr[A_1\cap C_1\cap A_2\cap C_2]=\phi^2c^2$; inclusion–exclusion gives $\Pr[D_A]$. Each sample is an independent Bernoulli trial with the same success probability because samples are random and sequenced to the same depth, so $K$ is binomial. The trade-off behind Theorem 3 is that more samples raise the chance that the rare variant is present at all, while lower per-sample depth lowers $c(R/\sigma,\tau)$.

## Sources

- M. C. Wendl, R. K. Wilson, "The theory of discovering rare variants via DNA sequencing", BMC Genomics 10 (2009) 485. <https://doi.org/10.1186/1471-2164-10-485>, PMCID PMC2778663. Theorems 1–3 and their proofs.
