# Bipartition hidden Markov model for genotype likelihoods

**Generative model.** For a read bipartition $B = (B^1,B^2)$ of an alignment matrix $M$ and a diplotype $H = (H^1,H^2)$, sites are independent and the two haplotype alleles descend from an ancestral allele $Z_j$:

$$P(H \mid B, M) = \prod_{j=1}^n \sum_{Z_j \in \Sigma_j} P(H^1_j \mid B^1, Z_j)\,P(H^2_j \mid B^2, Z_j)\,P(Z_j),$$

$$P(H^k_j \mid B^k, Z_j) = \frac{P(H^k_j \mid Z_j)\prod_{i \in B^k:\,M_{i,j}\ne -} P(M_{i,j} \mid H^k_j)}{\sum_{Y_j\in\Sigma_j} P(Y_j\mid Z_j)\prod_{i\in B^k:\,M_{i,j}\ne -}P(M_{i,j}\mid Y_j)},$$

with $P(H^k_j \mid Z_j)$ a substitution model (e.g. Jukes–Cantor) and $P(M_{i,j}\mid H^k_j)$ a read-error model. The genotyping problem is $\arg\max_{H^1_j,H^2_j} \sum_B P(H^1_j,H^2_j \mid B, M)$ at each site.

**HMM.** Replace each vertex $B_j \in \mathcal B_j$ of the diploid path graph by states $(B_j, a_1, a_2) \in \mathcal B_j \times \Sigma_j \times \Sigma_j$, keep the silent bipartition states $\mathcal C_j$, and give each edge out of $\mathcal C_j$ (or start) into $(B_j,a_1,a_2)$ the probability $P(a_1,a_2) = \sum_{Z_j} P(a_1\mid Z_j)P(a_2 \mid Z_j)P(Z_j)$; all other edges have probability $1$. State $(B_j,a_1,a_2)$ emits the non-gap entries of column $j$, reads in $B^k_j$ being drawn from allele $a_k$.

**Proposition (posterior state probabilities).** With forward and backward variables $\alpha_j, \beta_j$,

$$P\big((B,a_1,a_2) \mid M\big) = \frac{\alpha_j(B,a_1,a_2)\,\beta_j(B,a_1,a_2)}{\sum_{B' \in \mathcal B(A_j)}\sum_{a'_1,a'_2 \in \Sigma_j} \alpha_j(B',a'_1,a'_2)\,\beta_j(B',a'_1,a'_2)},$$

and the likelihood of a genotype at site $j$ is the sum of these posteriors over all bipartitions and all ordered allele pairs giving that unordered genotype.

## Depends on

- [Diploid path graph of read bipartitions](diploid-path-graph-of-read-bipartitions.md)

## Expansion

By the diploid-path lemma, summing over HMM paths is summing over all read bipartitions and allele assignments, so forward–backward computes the marginal over $B$ exactly in time linear in $n$ and exponential only in coverage. Because reads spanning several variants are forced to one haplotype, linked sites share evidence, which is why haplotype-aware genotyping corrects calls that single-site pileup methods get wrong on error-prone long reads. The Viterbi path gives the most probable bipartition and hence a phased diplotype.

## Sources

- J. Ebler, M. Haukness, T. Pesout, T. Marschall, B. Paten, "Haplotype-aware diplotyping from noisy long reads", Genome Biology 20 (2019) 116, Methods (genotype inference problem overview; HMM for genotype and diplotype inference; computing genotype likelihoods), Eq (1), <https://doi.org/10.1186/s13059-019-1709-0>, PMCID PMC6547545.
