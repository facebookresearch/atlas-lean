# Counting-partition reduction for IBD between g-degree relatives

**Inheritance model.** Two individuals descend from a common ancestor through chains of $g$
meioses each. In the 4-track model, the hidden state at a SNP locus consists of binary selectors
$S^a = (S^a_0, \dots, S^a_g)$ and $S^b = (S^b_0, \dots, S^b_g)$ recording which parental allele is
transmitted at each meiosis along the two chains, together with founder alleles $f = (f_1, f_2, f_3,
f_4)$ ($f_1, f_2$ those of the common ancestor). Along the genome, each selector switches state
between adjacent loci at distance $l$ Morgans with probability $\theta = 1 - e^{-l}$, independently
(a factorial hidden Markov model), and linkage disequilibrium enters through Markov transition terms
$P(f_i \mid f_{i-1})$ for founder alleles. The naive state space has size $O(2^{2g})$.

**Counting partition.** For a cluster $C$ of $r$ selectors, let class $[j]$ contain the
$\binom{r}{j}$ selector vectors with exactly $j$ entries "on". From a vector with $j$ entries on, the
probability of moving to class $[i]$ is

$$P([i] \mid c_j) = \sum_{t = \max(0,\, i + j - r)}^{\min(i, j)} \binom{j}{t} \binom{r - j}{i - t}\,
 \theta^{\,i + j - 2t} (1 - \theta)^{\,r - i - j + 2t},$$

where $t$ counts selectors on in both vectors; it depends on $c_j$ only through $j$.

**Theorem 1.** For any partition of the selectors into disjoint clusters, the factorial HMM whose
hidden variable ranges over $[C_1] \times \cdots \times [C_m] \times F$, with $[C_l]$ the counting
partition of cluster $C_l$ and $F$ any fixed founder-allele state space carrying LD transition terms,
satisfies the lumpability condition (Condition II).

**Theorem 2.** In the 4-track model, let $S^a_C$ be "on" iff $S^a_1 = \cdots = S^a_g =$ on, and
define $S^b_C$ likewise. Then the likelihood of the SNP data at a locus depends on the selectors only
through $(S^a_C, S^a_0, S^b_C, S^b_0)$, together with the founder alleles and the allele frequencies
(Condition I).

**Theorem 3.** Consequently, the likelihood of the 4-track model is computed exactly on a reduced
state space of size $2^4 \times g \times g$, in time $O(g^2 \log g)$ per locus.

## Depends on

- [Lumped hidden Markov likelihood under state equivalence](lumped-hidden-markov-likelihood-under-state-equivalence.md)

## Expansion

The transition formula counts the $\binom{j}{t}$ ways to keep $t$ of the $j$ "on" selectors and the
$\binom{r-j}{i-t}$ ways to switch $i - t$ "off" selectors on, each choice requiring $i + j - 2t$
switches; since the result depends only on $j$, the counting partition is lumpable, and the founder
LD factor is untouched by the reduction. Condition I holds because an allele reaches a descendant
from the common ancestor only if every selector along its chain points towards that ancestor, so
whether the two genotyped individuals share alleles identical by descent depends only on the
indicators $S^a_C$, $S^b_C$ and the top-generation selectors. By the lumping proposition, the
reduced model gives the same likelihood and the same posterior IBD probabilities while modelling LD
explicitly, so identical-by-state stretches in high-LD regions are no longer mistaken for IBD.

## Sources

- S. Bercovici, C. Meek, Y. Wexler, D. Geiger, "Estimating genome-wide IBD sharing from SNP data via
  an efficient hidden Markov model of LD with application to gene mapping", Bioinformatics 26 (2010)
  i175-i182, Sections 2-4, Eqs. (2) and (5), Theorems 1-3,
  <https://doi.org/10.1093/bioinformatics/btq204> (PMC2881389).
