# Relative accuracy of a polygenic score across ancestries

Let a polygenic score (PGS) be built from $M_T$ approximately independent genome-wide significant SNPs whose effects are estimated by GWAS in population $1$, and let a trait have $M_C$ causal variants. For $l \in \{1,2\}$ write $p_{k,l}$ for the minor-allele frequency of PGS-SNP $k$ in population $l$, $r_{jk,l}$ for the LD correlation between causal variant $j$ and PGS-SNP $k$ in population $l$, $h_l^2$ for the trait heritability in population $l$, and $\rho_b$ for the correlation of causal effects between the populations. Let $R_l^2$ be the squared correlation between the PGS and the trait in a target sample of ancestry $l$.

**Assumptions.** The trait is additive, $y_l = \sum_{j=1}^{M_C}\beta_{j,l}\,(x_{j,l} - 2p^{(c)}_{j,l})/\sqrt{2p^{(c)}_{j,l}(1-p^{(c)}_{j,l})} + e_l$, with $x_{j,l}$ the minor-allele count and $p^{(c)}_{j,l}$ the minor-allele frequency of causal variant $j$ in population $l$, and $e_l$ a non-genetic residual. The $M_C$ causal variants are shared between the populations (an ancestry-specific variant is one whose effect is zero in the other population). Phenotypes are scaled so that $\operatorname{var}(y_1) = \operatorname{var}(y_2) = 1$, so $h_l^2$ is the genetic variance in population $l$. Effects per standardized genotype are independent across variants and bivariate normal,

$$\begin{pmatrix}\beta_{j,1}\\ \beta_{j,2}\end{pmatrix} \sim \mathcal{N}\!\left(\begin{pmatrix}0\\ 0\end{pmatrix},\ \frac{1}{M_C}\begin{pmatrix}h_1^2 & \rho_b h_1h_2\\ \rho_b h_1h_2 & h_2^2\end{pmatrix}\right),$$

so each causal variant explains the same expected variance whatever its allele frequency. The PGS uses the same weights, marginal effects estimated in population $1$, at $M_T$ independent genome-wide significant SNPs in both populations. Under these assumptions the relative accuracy satisfies, approximately,

$$\frac{R_2^2}{R_1^2} \approx \frac{\rho_b^2 h_2^2}{h_1^2} \times \left(\frac{\sum_{k=1}^{M_T}\sqrt{\dfrac{p_{k,2}(1-p_{k,2})}{p_{k,1}(1-p_{k,1})}}\,\Bigl[\sum_{j=1}^{M_C} r_{jk,1}\, r_{jk,2}\Bigr]}{\sum_{k=1}^{M_T}\Bigl(\sum_{j=1}^{M_C} r_{jk,1}^2\Bigr)}\right)^2 \times \frac{\operatorname{var}(\mathrm{PGS}_1)}{\operatorname{var}(\mathrm{PGS}_2)} .$$

The four factors are the squared cross-ancestry correlation of causal effects, the heritability ratio, the ratio of squared PGS–trait covariances, which depends on LD and allele-frequency differences, and the ratio of PGS variances. When causal variants are unknown, the inner sums over $j$ are replaced by averages over candidate causal SNPs near each PGS-SNP.

## Proof sketch

Write $R_l^2 = \operatorname{cov}(\mathrm{PGS}_l, y_l)^2 / (\operatorname{var}(\mathrm{PGS}_l)\operatorname{var}(y_l))$. The PGS weights are the same in both populations. Taking expectations over the independent normal effects, the covariance of the score with the genetic value is a sum over PGS-SNPs of the estimated weight times the causal effects tagged through LD. On the standardized scale, moving from population $1$ to population $2$ rescales each SNP by the ratio of genotype standard deviations, which is the square-root MAF factor, and replaces the tagging $\sum_j r_{jk,1}^2$ by $\sum_j r_{jk,1}r_{jk,2}$. Correlated rather than identical causal effects contribute $\rho_b$, and normalizing by the trait variance contributes $h_2^2/h_1^2$. Squaring the covariance ratio and dividing by the PGS variance ratio gives the formula. With identical populations every factor is $1$.

## Sources

- Y. Wang, J. Guo, G. Ni, J. Yang, P. M. Visscher, L. Yengo, *Theoretical and empirical quantification of the accuracy of polygenic scores in ancestry divergent populations*, Nature Communications 11 (2020), 3865, <https://doi.org/10.1038/s41467-020-17719-y>, PMCID PMC7395791. Eq. (1); candidate-causal-variant approximation Eq. (2); model, assumptions and derivation in Supplementary Note 1 (Eqs. (1)–(5)).
