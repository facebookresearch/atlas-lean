# Distance-covariance test for SNP–SNP dependence and epistasis

**Setting.** Each single-nucleotide polymorphism (SNP) has genotype space $\{0,1,2\}$ (number of minor alleles). Nothing guarantees that two minor alleles act twice as strongly as one (heterozygote effects exist), so instead of the Euclidean metric $d(0,2) = 2d(0,1) = 2d(1,2)$ one may use the **discrete metric** $d(0,1) = d(1,2) = d(0,2) = 1$, which assumes no genetic model. Premetrics encode inheritance modes: recessive $d(0,1) = 0$, $d(0,2) = d(1,2) = 1$; dominant $d(1,2) = 0$, $d(0,1) = d(0,2) = 1$; heterozygous $d(0,2) = 0$, $d(0,1) = d(1,2) = 1$. Every three-point metric space has strong negative type, so the distance covariance $\mathrm{dCov}(X,Y)$ vanishes iff $X$ and $Y$ are independent. Its empirical version is $\widehat{\mathrm{dCov}}^2 = n^{-2}\sum_{i,j}\tilde D^X_{ij}\tilde D^Y_{ij}$, where $\tilde D$ is the doubly centered within-sample distance matrix.

**Epistasis test.** Epistasis between SNPs $i$ and $j$ appears as a difference in their dependence structure between cases and controls. In each group one tests $H_0 : \mathrm{dCov}(Z_i,Z_j) = 0$ against $H_1 : \mathrm{dCov}(Z_i,Z_j) \ne 0$, then compares the groups within a large-scale multiple-testing framework.

**Theorem (asymptotic null law).** Let $(X_k,Y_k)_{k\le n}$ be i.i.d. pairs of genotypes in $\{0,1,2\}^2$ with marginal probabilities $p_j = \Pr(X = j)$ and $q_j = \Pr(Y = j)$. If $X$ and $Y$ are independent then, as $n \to \infty$,

$$ n\,\widehat{\mathrm{dCov}}^2(X,Y) \xrightarrow{d} \sum_{a,b\in\{1,2\}}\lambda_a\mu_b\,Z_{ab}^2, \qquad Z_{ab}^2 \overset{\text{iid}}{\sim} \chi^2_1, $$

with the following eigenvalues:
- discrete metric: $\lambda_{1,2} = \dfrac{1 - \sum_j p_j^2}{2} \pm \sqrt{\dfrac{(1 - \sum_j p_j^2)^2}{4} - 3\,p_0p_1p_2}$, and $\mu_{1,2}$ the same expression in $q$;
- Euclidean metric: $\lambda_{1,2} = s_p \pm \sqrt{s_p^2 - 4\,p_0p_1p_2}$ with $s_p = p_0(1-p_0) + p_2(1-p_2)$, and $\mu_{1,2}$ the same expression in $q$.

The general fact behind this is that, for finitely supported $X$ and $Y$, the null limit is the quadratic form with coefficients $\lambda^X_a\lambda^Y_b$, the products of the nonzero eigenvalues of $L^X_{rs} = p_s\big(\delta_{rs} - p_r - p_s + \sum_i p_i^2\big)$ and of its analogue for $Y$. The paper's display repeats $\lambda_1\mu_2$ in the fourth term; the product structure gives $\lambda_2\mu_2$. Because only four $\chi^2$ terms are nonzero, p-values come from an explicit weighted-$\chi^2$ law instead of permutations, which makes genome-wide pairwise scans feasible. The thesis applies the test to a case–control study of schizophrenia, and extends it to more than two SNPs and to gene–phenotype association with SNP-tailored premetrics.

## Expansion

Distance covariance is a degenerate V-statistic. Under independence its kernel factorizes into the doubly centered distance kernels of $X$ and $Y$, so $n\widehat{\mathrm{dCov}}^2$ converges to $\sum\lambda_a\mu_b Z_{ab}^2$, where $\lambda_a$ and $\mu_b$ are the eigenvalues of the centered distance operators. On a three-point space these operators are $3\times 3$ matrices of rank at most $2$, and their nonzero eigenvalues solve a quadratic equation with trace $\frac12(1 - \sum p_j^2)$ (discrete metric) and determinant proportional to $p_0p_1p_2$. This gives the closed forms above.

## Sources

- Fernando Castro-Prado, "Nonparametric independence tests in high-dimensional settings, with applications to the genetics of complex disease", arXiv:2407.19624 (2024), chapter "Testing for gene-gene interactions in complex disease" (sections on distance correlation in spaces of cardinality 3 and on the proposed test, with its two asymptotic-null theorems for the discrete and Euclidean metrics); appendix chapter "Some theoretical results" (lemma on the discrete distance), <https://doi.org/10.48550/arXiv.2407.19624>.
