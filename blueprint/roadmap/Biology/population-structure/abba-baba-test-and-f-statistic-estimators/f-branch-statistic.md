# The f-branch statistic

Fix a rooted phylogeny of populations with outgroup $O$. For populations $P_1, P_2, P_3$ the
[$f_4$-ratio](../patterson-s-f-statistics/f4-ratio.md) estimate of the admixture proportion from $P_3$ into $P_2$
relative to $P_1$ is

$$f_4\text{-ratio}(P_1, P_2; P_3, O) = \frac{\sum_{i} (\hat p_{i3a} - \hat p_{iO})(\hat p_{i2} - \hat p_{i1})}{\sum_{i} (\hat p_{i3a} - \hat p_{iO})(\hat p_{i3b} - \hat p_{i1})},$$

where $P_3$ is split into two halves $P_{3a}, P_{3b}$ (alleles sampled at random at each site). For a branch $b$ of the tree, let
$\mathcal B$ be the set of populations descending from $b$ and $\mathcal A$ the set descending from the sister branch of $b$. The
source computes the statistic over the positive $f_4$-ratio results with $A \in \mathcal A$ in the $P_1$ and $B \in \mathcal B$ in
the $P_2$ position; here a non-positive result is recorded as $0$, that is, write

$$f_4^+(A, B; C, O) = \max\bigl(f_4\text{-ratio}(A, B; C, O),\, 0\bigr).$$

For a population $C$ outside $\mathcal A \cup \mathcal B$, the **f-branch statistic** is

$$f_b(C) = \operatorname{median}_{A \in \mathcal A} \Bigl( \min_{B \in \mathcal B}\ f_4^+(A, B; C, O) \Bigr),$$

the minimum over the descendants $B$ of the focal branch $b$ taken first, then the median over the descendants $A$ of its sister
branch. The two operations do not commute in general, so the order matters.

It measures excess allele sharing between $C$ and the lineage $b$, relative to its sister lineage. Taking the minimum over
$B$ removes signal produced by gene flow into a single sublineage of $\mathcal B$, keeping only what every descendant of $b$ shares;
taking the median over $A$ discounts a few sister descendants whose own gene flow with $C$ distorts the comparison. A high $f_b(C)$
is consistent with gene flow between $C$ and branch $b$ itself, possibly an internal branch, but excess sharing alone does not
determine the direction of gene flow or identify a unique event on $b$.

## Depends on

- [f4-ratio estimation of the admixture proportion](../patterson-s-f-statistics/f4-ratio.md)

## Proof depends on

- [Bias factor of the f4 ratio in the drift model](../bias-of-the-f4-ratio-estimator/f4-ratio-eq-mul-div.md)

## Expansion

When gene flow from $C$ entered the ancestor on branch $b$, every descendant $B \in \mathcal B$ inherits the same admixture fraction,
so every $f_4$-ratio$(A, B; C, O)$ with $A$ from the sister clade is elevated, by the bias-factor identity for the $f_4$ ratio in the
drift model, and both the minimum over $B$ and the median over $A$ retain it. If instead gene flow entered only one descendant
$B_0$ and $|\mathcal B| \ge 2$, the minimum over $B$ picks a descendant $B \ne B_0$ and removes it. If gene flow involved one
descendant $A_0$ of the sister clade, it changes only the entries with $A = A_0$; when $|\mathcal A| \ge 3$, changing one value
moves the median over $\mathcal A$ only within the range of the other values, however large the change. The statistic thus condenses the many correlated trio results into one value per (branch, population)
pair. (Malinsky, Matschiner and Svardal 2021, Equation 6 and the f-branch section; statistic introduced by Malinsky et al. 2018.)

## Sources

- M. Malinsky, M. Matschiner, and H. Svardal, "Dsuite ‐ Fast D ‐statistics and related admixture evidence from VCF files", Molecular Ecology Resources (2020), <https://doi.org/10.1111/1755-0998.13265> (PMC7116594).
- M. Malinsky, H. Svardal, A. M. Tyers et al., "Whole-genome sequences of Malawi cichlids reveal multiple radiations interconnected by gene flow", Nature Ecology & Evolution 2 (2018), 1940–1955, <https://doi.org/10.1038/s41559-018-0717-x>.
