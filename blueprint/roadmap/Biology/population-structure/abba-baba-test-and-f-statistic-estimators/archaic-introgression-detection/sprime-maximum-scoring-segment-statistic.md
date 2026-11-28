# Sprime maximum-scoring segment statistic

**Setup.** Take phased or unphased genotypes of a target sample and of an outgroup that is closely related to the target's ancestors but has received (almost) no admixture from the archaic source. On one chromosome, discard alleles with outgroup frequency above $0.01$ and order the remaining alleles $v_1, \dots, v_V$ by position. For a pair of alleles $(v_a, v_b)$ let $X_{ia}, X_{ib} \in \{0,1,2\}$ be their doses in target individual $i$, and put

$$D = \sum_i \lvert X_{ia} - X_{ib}\rvert, \qquad n = \min\Big(\sum_i X_{ia},\ \sum_i X_{ib}\Big),$$

the count of apparent recombination breakpoints between the two alleles and the smaller carrier-haplotype count. Let $m$ be the local mutation rate per centimorgan per meiosis and $w = 1$ if the outgroup frequency of $v_b$ is $0$, $w = 0.8$ if it lies in $(0, 0.01]$.

**Pairwise score.**

$$T(v_a, v_b) = 6000\, w\,\frac{1 - e^{-0.01/m}}{1 - e^{-1}} - 25000\,\frac{D}{n},$$

with $T = -\infty$ if the alleles are more than $20$ kb or fewer than $10$ bp apart, or if they share no carriers ($\sum_i X_{ia}X_{ib} = 0$). The first term rewards high-LD pairs more in regions with few mutations per unit genetic length (for large $m$ it behaves like $0.01/((1 - e^{-1})m) \approx 1/(63m)$, and it is bounded by $1/(1 - e^{-1}) \approx 1.58$ times $6000$); the second penalizes breakpoints relative to the introgressed haplotype's frequency, since common introgressed haplotypes accumulate proportionally more recombinations.

**Segment score and its maximization.** A set of alleles $a_1 < \dots < a_J$ scores $S(a_1, \dots, a_J) = \sum_{j=1}^{J-1} T(a_j, a_{j+1})$. Define $S_1^* = 0$ and

$$S_{j+1}^* = \max\Big\{0,\ \max_{1 \le k \le j}\big(S_k^* + T(v_k, v_{j+1})\big)\Big\}.$$

Then $S_j^*$ is the maximal score of a set ending at $v_j$, and $\max_j S_j^*$ is the maximal segment score, attained by back-tracking the maximizing indices. Sprime reports this set as a putative introgressed segment of archaic-specific alleles, removes its alleles, and repeats until the best remaining score falls below a threshold (default $150{,}000$).

## Remarks

The recursion is the dynamic program for a maximum-weight path in a directed acyclic graph whose vertices are the alleles in positional order and whose arcs $v_k \to v_{j}$ ($k < j$) carry weight $T(v_k, v_j)$: an optimal set ending at $v_{j+1}$ either starts there (score $0$) or extends an optimal set ending at its predecessor $v_k$, and since $S$ is a sum over consecutive pairs, optimal substructure holds. The cost is $O(V^2)$ in the worst case, reduced in practice because $T = -\infty$ beyond $20$ kb. Two alleles on the same introgressed haplotype have $X_{ia} = X_{ib}$ for every individual unless a recombination between introgressed and non-introgressed haplotypes falls between them on one of individual $i$'s lineages, which is why $D$ counts breakpoints. The local rate $m$ is estimated as (local variant density / genome-wide variant density) times the genome-wide mutation rate, times the local base pairs per centimorgan from a linkage-disequilibrium map, taking conservative maxima over nested windows. The archaic genome is used only afterwards, to validate segments by their match rate.

## Sources

- S. R. Browning, B. L. Browning, Y. Zhou, S. Tucci and J. M. Akey, "Analysis of Human Sequence Data Reveals Two Pulses of Archaic Denisovan Admixture", *Cell* 173 (2018), 53–61.e9, STAR Methods "Details of the Sprime algorithm" (S*-type scoring, pairwise score function), <https://doi.org/10.1016/j.cell.2018.02.031> (PMC5866234).
- V. Plagnol and J. D. Wall, "Possible ancestral structure in human populations", *PLoS Genetics* 2 (2006), e105, <https://doi.org/10.1371/journal.pgen.0020105> (original S* dynamic program).
