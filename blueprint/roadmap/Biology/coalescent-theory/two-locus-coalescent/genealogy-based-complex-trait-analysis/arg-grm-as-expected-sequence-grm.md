# ARG genetic relationship matrix as an expected sequence-based GRM

Consider $N$ haploid genomes with genotypes $x_{ik} \in \{0,1\}$ at $M$ variant sites, where $p_k$ is the sample frequency of variant $k$. Under an infinitesimal architecture in which per-allele effects satisfy $\operatorname{Var}(\beta_k) \propto (p_k(1-p_k))^{\alpha}$, the genetic relationship matrix (GRM) is

$$K^{\alpha}_{ij} = \frac1M\sum_{k=1}^{M}(x_{ik} - p_k)(x_{jk} - p_k)\bigl(p_k(1-p_k)\bigr)^{\alpha},$$

that is, the centred genotype product divided by $(p_k(1-p_k))^{-\alpha}$; the usual standardized GRM is $\alpha = -1$, and more negative $\alpha$ weights rare variants more. For $\alpha = 0$ it is determined by the **Hamming distance matrix** $D_{ij} = \frac1M\sum_k x_{ik} \oplus x_{jk}$, which has zero diagonal and is not itself a covariance: with $J = I - \mathbf 1\mathbf 1^\top/N$,

$$K^{0} = -\tfrac12\, J D J .$$

Given an ARG with pairwise TMRCA $t_{ijk}$ at base pair $k$ of a genome of $L$ base pairs, and mutations arising as a Poisson process of rate $\mu$ per base pair per generation uniformly over the ARG, the expected per-base-pair sequence distance is

$$D^{\mathrm{ARG}}_{ij} = \frac1L\sum_{k=1}^{L}\Pr\bigl(\mathrm{Poisson}(2\mu t_{ijk}) > 0\bigr) = \frac1L\sum_{k=1}^{L}\bigl(1 - e^{-2\mu t_{ijk}}\bigr) \approx \frac{2\mu}{L}\sum_{k=1}^{L} t_{ijk},$$

a distance, proportional for small $\mu$ to the genome-wide sum of pairwise TMRCAs. The **ARG-GRM** for $\alpha = 0$ is the conditional expectation of the relationship above,

$$K^{\mathrm{ARG}} = \mathbb E\bigl[-\tfrac12 J D^{\mathrm{seq}} J \bigm| \mathrm{ARG}\bigr] = -\tfrac12\, J D^{\mathrm{ARG}} J,$$

where $D^{\mathrm{seq}}$ is the per-base-pair Hamming distance of the sequences the ARG would generate; the untransformed TMRCA sum is the distance, not the covariance. In practice a Monte Carlo ARG-GRM is built by sampling mutations on the ARG at a high rate and applying the $K^{\alpha}$ formula, with weight $(p_k(1-p_k))^{\alpha}$, to the sampled variants; the Monte Carlo matrix converges to the exact one as the sampling rate grows (saturating near $\mu \approx 1.65 \times 10^{-7}$ in simulations), and stratifying sampled mutations by allele frequency gives robust heritability estimates when $\alpha$ is unknown.

## Depends on

- [Genetic relationship matrix](../../../statistical-genetics/greml-and-haseman-elston-estimation-of-snp-herit/grm.md)
- [Genome ARGs: interval-annotated inheritance graphs and their local trees](../genome-arg-interval-annotated-inheritance-graph.md)

## Expansion

At base pair $k$, genomes $i$ and $j$ differ exactly when a mutation falls on the path joining them in the marginal tree, whose length is $2t_{ijk}$ (from each leaf up to their common ancestor); under infinite sites the probability of at least one mutation is $1 - e^{-2\mu t_{ijk}}$. For binary genotypes $x_i \oplus x_j = (x_i - x_j)^2 = (x_i - p)^2 + (x_j - p)^2 - 2(x_i - p)(x_j - p)$, so $D_{ij} = K^0_{ii} + K^0_{jj} - 2K^0_{ij}$. Double centring removes the terms that depend on $i$ or on $j$ alone, and $J K^0 J = K^0$ because each column of centred genotypes sums to zero over the sample, which gives $K^0 = -\frac12 J D J$; conversely $D$ is recovered from $K^0$ by the first identity. Because $J$ is fixed and the map is linear, the expectation passes through it, which is the formula for $K^{\mathrm{ARG}}$. The ARG-GRM thus predicts the GRM that whole-genome sequencing would give, including rare variants that a genotyping array misses but that the genealogy implies.

## Sources

- B. C. Zhang, A. Biddanda, Á. F. Gunnarsson, F. Cooper, P. F. Palamara, "Biobank-scale inference of ancestral recombination graphs enables genealogical analysis of complex traits", Nature Genetics 55 (2023), Methods ("Construction of ARG-GRMs", Equation (1)) and Extended Data Fig. 7, <https://doi.org/10.1038/s41588-023-01379-x> (PMC10181934).
