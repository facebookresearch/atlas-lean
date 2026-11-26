# ARG genetic relationship matrix as an expected sequence-based GRM

Consider $N$ haploid genomes with genotypes $x_{ik} \in \{0,1\}$ at $M$ sites, where variant $k$ has mean $p_k$. Under an infinitesimal architecture in which per-allele effects satisfy $\operatorname{Var}(\beta_k) \propto (p_k(1-p_k))^{\alpha}$, the genetic relationship matrix (GRM) is

$$K^{\alpha}_{ij} = \frac1M\sum_{k=1}^{M}(x_{ik} - p_k)(x_{jk} - p_k)\bigl(p_k(1-p_k)\bigr)^{-\alpha}.$$

For $\alpha = 0$ this carries the same information as the Hamming matrix $K^H_{ij} = \frac1M\sum_k x_{ik} \oplus x_{jk}$ (up to the invariances of double centring). Given an ARG with pairwise TMRCA $t_{ijk}$ at base pair $k$ of a genome of $L$ base pairs, and mutations arising as a Poisson process of rate $\mu$ per base pair per generation uniformly over the ARG, the **ARG-GRM** is the expected sequence-based matrix

$$K^{\mathrm{ARG}}_{ij} = \mathbb E\bigl[K^H_{ij} \mid \mathrm{ARG}\bigr] \ \propto\ \sum_{k=1}^{L}\Pr\bigl(\mathrm{Poisson}(2\mu t_{ijk}) > 0\bigr) = \sum_{k=1}^{L}\bigl(1 - e^{-2\mu t_{ijk}}\bigr) \approx 2\mu\sum_{k=1}^{L} t_{ijk},$$

so for $\alpha = 0$ it is proportional to the genome-wide sum of pairwise TMRCAs. In practice a Monte Carlo ARG-GRM is built by sampling mutations on the ARG at a high rate and applying the $K^{\alpha}$ formula to them; the Monte Carlo matrix converges to the exact one as the sampling rate grows (saturating near $\mu \approx 1.65 \times 10^{-7}$ in simulations), and stratifying sampled mutations by allele frequency gives robust heritability estimates when $\alpha$ is unknown.

## Depends on

- [Genetic relationship matrix](../../statistical-genetics/greml-and-haseman-elston-estimation-of-snp-herit/grm.md)

## Expansion

At base pair $k$, genomes $i$ and $j$ differ exactly when a mutation falls on the path joining them in the marginal tree, whose length is $2t_{ijk}$ (from each leaf up to their common ancestor); under infinite sites the probability of at least one mutation is $1 - e^{-2\mu t_{ijk}}$. For binary genotypes $(x_i - x_j)^2 = x_i \oplus x_j$ and $(x_i - x_j)^2 = (x_i - p)^2 + (x_j - p)^2 - 2(x_i - p)(x_j - p)$, so the $\alpha = 0$ GRM and the Hamming matrix determine each other after centring. The ARG-GRM thus predicts the GRM that whole-genome sequencing would give, including rare variants that a genotyping array misses but that the genealogy implies.

## Sources

- B. C. Zhang, A. Biddanda, Á. F. Gunnarsson, F. Cooper, P. F. Palamara, "Biobank-scale inference of ancestral recombination graphs enables genealogical analysis of complex traits", Nature Genetics 55 (2023), Methods ("Construction of ARG-GRMs", Equation (1)) and Extended Data Fig. 7, <https://doi.org/10.1038/s41588-023-01379-x> (PMC10181934).
