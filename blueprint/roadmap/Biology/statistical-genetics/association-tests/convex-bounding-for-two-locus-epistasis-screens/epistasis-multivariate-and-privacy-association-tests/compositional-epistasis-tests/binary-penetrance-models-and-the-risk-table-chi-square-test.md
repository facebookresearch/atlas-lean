# Binary penetrance models and the risk-table chi-square test

For two biallelic SNPs with genotypes coded $1, 2, 3$, a *compositional epistasis model* is a $3\times3$ penetrance table $(p_{ij})$ with every $p_{ij} \in \{0, 1\}$, meaning low or high risk for the joint genotype $(i,j)$. There are $2^9 = 512$ such tables, labelled by the binary number $(p_{11}p_{12}p_{13}p_{21}p_{22}p_{23}p_{31}p_{32}p_{33})_2$; the dominant-dominant model (high risk iff both SNPs carry a minor allele) has label $(000011011)_2 = 27$, and up to the symmetries of relabelling there are 51 distinct patterns. Given a case-control sample with genotype counts $n_{ij0}$ (controls) and $n_{ij1}$ (cases), a model collapses the $3\times3\times2$ table into the $2\times2$ risk table

$$a = \sum_{p_{ij}=0} n_{ij0},\quad b = \sum_{p_{ij}=1} n_{ij0},\quad c = \sum_{p_{ij}=0} n_{ij1},\quad d = \sum_{p_{ij}=1} n_{ij1},$$

and its fit is tested by Pearson's statistic

$$X^2 = \frac{(ad - bc)^2\,(a+b+c+d)}{(a+b)(c+d)(a+c)(b+d)},$$

which is asymptotically $\chi^2_1$ under independence of risk group and disease status. Because the test has one degree of freedom whatever the model, it keeps power when low minor-allele frequencies leave genotype cells sparse, where the 4-df interaction and 8-df full-association logistic tests lose their nominal degrees of freedom.

## Depends on

- [Pearson's chi-squared statistic of a 2 × 2 table](../../../../genomic-prediction-from-summary-statistics/pearson2x2.md)

## Proof depends on

- [Asymptotic law of the Pearson chi-square test of independence](../../../../../../Probability/hypothesis-testing/score-wald-and-likelihood-ratio-tests/pearson-chi-square-test-of-independence.md)

## Expansion

Every non-constant binary penetrance table is a bipartition of the nine joint genotypes into low- and high-risk groups, and the risk table is the $2\times 2$ table of group by status. The closed form of $X^2$ is the usual one for a $2\times2$ table. Since the best of many models is reported, multiplicity must be accounted for; the sorted-ratio split shows that the maximum over all models is attained among 8 candidates.

## Sources

- X. Wan, C. Yang, Q. Yang, H. Zhao and W. Yu, "The complete compositional epistasis detection in genome-wide association studies", BMC Genetics 14 (2013), 7, <https://doi.org/10.1186/1471-2156-14-7>, PMCID PMC3638013. Tables 1–4 and Eq. (4); the count of 51 patterns is from Li and Reich, Hum. Hered. 50 (2000).
