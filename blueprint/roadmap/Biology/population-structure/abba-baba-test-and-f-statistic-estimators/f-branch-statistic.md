# The f-branch statistic

Fix a rooted phylogeny of populations with outgroup $O$. For populations $P_1, P_2, P_3$ the
[$f_4$-ratio](../bias-of-the-f4-ratio-estimator/f4-ratio-eq-mul-div.md) estimate of the admixture proportion from $P_3$ into $P_2$
relative to $P_1$ is

$$f_4\text{-ratio}(P_1, P_2; P_3, O) = \frac{\sum_{i} (\hat p_{i3a} - \hat p_{iO})(\hat p_{i2} - \hat p_{i1})}{\sum_{i} (\hat p_{i3a} - \hat p_{iO})(\hat p_{i3b} - \hat p_{i1})},$$

where $P_3$ is split into two halves $P_{3a}, P_{3b}$ (alleles sampled at random at each site). For a branch $b$ of the tree, let
$\mathcal B$ be the set of populations descending from $b$ and $\mathcal A$ the set descending from the sister branch of $b$. For a
population $C$ outside $\mathcal A \cup \mathcal B$, the **f-branch statistic** is

$$f_b(C) = \operatorname{median}_{B \in \mathcal B} \Bigl( \min_{A \in \mathcal A}\ f_4\text{-ratio}(A, B; C, O) \Bigr).$$

It measures excess allele sharing between $C$ and the lineage $b$, relative to its sister lineage. Taking the minimum over
$A$ removes signal produced by gene flow into a sublineage of $\mathcal A$; taking the median over $B$ discounts gene flow into a single
descendant of $b$, so a high $f_b(C)$ attributes the signal to branch $b$ itself, possibly an internal branch.

## Depends on

- [Frequency-based ABBA–BABA counts and the minimum D statistic of a trio](frequency-based-abba-baba-counts-and-dmin.md)
- [Bias factor of the f4 ratio in the drift model](../bias-of-the-f4-ratio-estimator/f4-ratio-eq-mul-div.md)

## Expansion

When gene flow from $C$ entered the ancestor on branch $b$, every descendant $B \in \mathcal B$ inherits the same admixture fraction,
so every $f_4$-ratio$(A, B; C, O)$ with $A$ from the sister clade is elevated and both the minimum and the median retain it. If
instead gene flow entered only one descendant $B_0$, the median over $\mathcal B$ is unaffected when $|\mathcal B| \ge 3$, and if it
entered a descendant $A_0$ of the sister clade, choosing $A \ne A_0$ in the minimum removes it. The statistic thus condenses the many
correlated trio results into one value per (branch, population) pair. (Malinsky, Matschiner and Svardal 2021, Equation for
$f_4$-ratio and the Fbranch section; statistic introduced by Malinsky et al. 2018.)

## Sources

- M. Malinsky, M. Matschiner, and H. Svardal, "Dsuite ‐ Fast D ‐statistics and related admixture evidence from VCF files", Molecular Ecology Resources (2020), <https://doi.org/10.1111/1755-0998.13265> (PMC7116594).
- M. Malinsky, H. Svardal, A. M. Tyers et al., "Whole-genome sequences of Malawi cichlids reveal multiple radiations interconnected by gene flow", Nature Ecology & Evolution 2 (2018), 1940–1955, <https://doi.org/10.1038/s41559-018-0717-x>.
