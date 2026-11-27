# MultiXcan joint regression on principal components of predicted expression

For one gene, let $W_j = (w_{aj})_a$ be the SNP weights of an expression-prediction model for tissue $j = 1, \dots, p$, let $X$ be the $n \times m$ genotype matrix of a GWAS, and let $t_j$ be the standardized predicted expression $\tilde t_j = X W_j$. With the centered phenotype $y \in \mathbb R^n$ and $T = (t_1, \dots, t_p)$, the **joint model** is

$$y = \sum_{j=1}^{p} t_j g_j + e = T g + e, \qquad e \sim (0, \sigma_e^2 I_n). \tag{2}$$

Because eQTLs are shared across tissues, $T^\top T$ is often nearly singular. MultiXcan therefore takes the eigendecomposition $T^\top T = \sum_i \lambda_i v_i v_i^\top$ and keeps only the components with condition number $\lambda_{\max}/\lambda_i < 30$. It regresses $y$ on the retained principal-component scores $T v_i$ and tests $H_0$: all retained coefficients are zero with the usual $F$-test on $k$ and $n - k - 1$ degrees of freedom, where $k$ is the number of retained components. Significance is assessed at a Bonferroni threshold over genes (one test per gene instead of one per gene–tissue pair).

**Joint estimates from marginal ones.** If $\hat\gamma_j$ is the slope of the marginal regression $y = t_j\gamma_j + \epsilon_j$ and $D = \mathrm{diag}(T^\top T)$, then $\hat\gamma = D^{-1}T^\top y$, so

$$\hat g = (T^\top T)^{-1}T^\top y = (T^\top T)^{-1} D\hat\gamma, \qquad \mathrm{var}(\hat g) = \sigma_e^2 (T^\top T)^{-1}, \tag{4, 8}$$

and for standardized $t_j$ one has $D = (n-1)I_p$.

## Remarks

The $F$-test compares the residual sum of squares of $y$ on the retained components with that of the intercept-only model. Since the components are orthogonal, this is a test that $y$ has no projection onto the span of the retained directions of predicted expression. Dropping directions of tiny variance $\lambda_i$ loses little power: a fixed effect along such a direction moves $y$ by only $O(\sqrt{\lambda_i})$. It also avoids the variance blow-up $\sigma_e^2/\lambda_i$ of the corresponding coefficient. The relation between joint and marginal slopes is the normal-equation identity $T^\top y = D\hat\gamma$. It lets the joint test be reconstructed from single-tissue results, which is the basis of the summary-statistic version.

## Sources

- A. N. Barbeira, M. Pividori, J. Zheng et al., "Integrating predicted transcriptome from multiple tissues improves association detection", PLoS Genetics 15 (2019), e1007889, Materials and Methods ("MultiXcan", Equation (2); "Joint analysis estimation from marginal effects", Equations (3)–(8)), <https://doi.org/10.1371/journal.pgen.1007889>, PMCID PMC6358100.
