# PESCA: two-population likelihood of GWAS z-scores given population-specific and shared causal SNPs

Consider $p$ SNPs and GWAS of one trait in two populations $j=1,2$ with sample sizes $n_j$. The causal status of SNP $i$ is a pair $C_i=(c_{i1},c_{i2})\in\{0,1\}^2$, where $c_{ij}=1$ means SNP $i$ has a nonzero effect in population $j$; $C_i=(1,1)$ is a shared causal SNP and $(1,0)$, $(0,1)$ are population-specific. The $C_i$ are independent across SNPs with a common bivariate Bernoulli law with natural parameters $f=(f_{00},f_{01},f_{10},f_{11})$, so $\Pr(C_1,\ldots,C_p)=\prod_{i=1}^p\Pr(C_i)$.

Let $c_j=(c_{1j},\ldots,c_{pj})^\top$, let $V_j$ be the $p\times p$ LD (correlation) matrix of population $j$, $h_{gj}^2$ the SNP-heritability and $|c_j|$ the number of causal SNPs in population $j$, and put

$$\sigma_j^2=\frac{n_jh_{gj}^2}{|c_j|}.$$

Assuming the z-score vectors $Z_1,Z_2\in\mathbb R^p$ are conditionally independent given $(c_1,c_2)$,

$$Z_j\mid c_j\sim\mathrm{MVN}\bigl(0,\ V_j+\sigma_j^2V_j\operatorname{diag}(c_j)V_j\bigr),$$

and the likelihood of $f$ is

$$\Pr(Z_1,Z_2;f)=\sum_{c_1}\sum_{c_2}\left[\prod_{i=1}^p\Pr\bigl(C_i=(c_{i1},c_{i2})\bigr)\prod_{j=1}^2\mathrm{MVN}\bigl(Z_j;0,V_j+\sigma_j^2V_j\operatorname{diag}(c_j)V_j\bigr)\right].$$

When the genome is partitioned into blocks that are approximately LD-independent in both populations, the likelihood is taken as the product of the block likelihoods. The parameters $f$ are fitted by an EM algorithm whose expectation step is approximated by Gibbs sampling over the causal configurations; the fitted $f^*$ gives the genome-wide proportions of population-specific and shared causal SNPs.

## Depends on

- [Posterior inclusion probability](pip.md)

## Expansion

- With standardized genotypes, the marginal z-score of population $j$ is $Z_j=\sqrt{n_j}\,V_j\beta_j+\epsilon_j$ with $\epsilon_j\sim\mathrm{MVN}(0,V_j)$. If the causal effects are independent $N(0,h_{gj}^2/|c_j|)$ on the causal set and zero elsewhere, then $\operatorname{Cov}(\beta_j)=(h_{gj}^2/|c_j|)\operatorname{diag}(c_j)$ and $\operatorname{Cov}(Z_j\mid c_j)=V_j+n_j(h_{gj}^2/|c_j|)V_j\operatorname{diag}(c_j)V_j$.
- Population-specific LD ($V_1\ne V_2$) lets a single non-causal SNP be GWAS-significant in both populations while the causal SNPs differ, which is why the model is fitted jointly rather than by comparing marginal signals.
- The conditional independence of $Z_1$ and $Z_2$ ignores any correlation of effect sizes at shared causal SNPs; this is a deliberate simplification.
- For the bivariate Bernoulli law in log-linear form, main-effect parameters $-3.9$ and an interaction $+3.9$ give each of the three nonnull configurations probability $e^{-3.9}/(1+3e^{-3.9})\approx1.9\%$; the paper initializes $f=(0,-3.9,-3.9,3.9)$, described as about 2% of SNPs causal in each configuration.

## Sources

- H. Shi, K. S. Burch, R. Johnson, et al., *Localizing components of shared transethnic genetic architecture of complex traits from GWAS summary data*, American Journal of Human Genetics 106 (2020), <https://doi.org/10.1016/j.ajhg.2020.04.012>, PMCID PMC7273527 (Material and Methods: Distribution of GWAS Summary Statistics in Two Populations, Equation 1; Estimating Genome-wide Proportions).
