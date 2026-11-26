# Cross-trait Laplacian-penalized least squares

**Model.** There are $K$ quantitative traits; trait $k$ is measured on $n_k$ independent individuals genotyped at the same $P$ SNPs, with trait $1$ the primary trait to be predicted. For individual $i$ of trait $k$,

$$y_{ki} = \alpha_k + \sum_{j=1}^{P} x_{kij}\beta_{kj} + \epsilon_{ki}, \qquad \epsilon_{ki}\sim N(0,\sigma_k^2),$$

typically with $P > n_k$. In addition, $M$ further traits may be available only as fixed per-SNP summary effect estimates $\hat s_{mj}$.

**Estimator.** With nonnegative adjacency weights $a_{kk'j}$ encoding prior similarity of the effect of SNP $j$ on traits $k$ and $k'$ (and $a_{k(K+m)j}$ for summary-statistic traits), the cross-trait penalized estimate is

$$\hat\beta = \arg\min_{\beta}\ \sum_{k=1}^{K}\frac{1}{2n_k}\sum_{i=1}^{n_k}\Big(y_{ki}-\alpha_k-\sum_{j=1}^{P}x_{kij}\beta_{kj}\Big)^2 + p^{\mathrm{sp}}_{\lambda_1}(\beta) + p^{\mathrm{ctp}}_{\lambda_2}(\beta),$$

where the sparsity penalty is either the Lasso $p^{\mathrm{sp}}_{\lambda_1}(\beta) = \lambda_1\sum_{k,j}|\beta_{kj}|$ or the minimax concave penalty (MCP)

$$p^{\mathrm{sp}}_{\lambda_1,\gamma}(\beta) = \lambda_1\sum_{k,j}\int_0^{|\beta_{kj}|}\Big(1-\frac{x}{\gamma\lambda_1}\Big)_+\,dx ,$$

and the cross-trait penalty is the Laplacian quadratic form

$$p^{\mathrm{ctp}}_{\lambda_2}(\beta) = \frac{\lambda_2}{2}\left[\sum_{\{k,k'\}}\sum_{j=1}^{P}a_{kk'j}\big(\beta_{kj}-\beta_{k'j}\big)^2 + \sum_{k=1}^{K}\sum_{m=1}^{M}\sum_{j=1}^{P}a_{k(K+m)j}\big(\beta_{kj}-\hat s_{mj}\big)^2\right],$$

the first sum running over unordered pairs of distinct individual-level traits.

**Properties.** With $\lambda_2 = 0$ the problem separates into $K$ independent penalized regressions. As $\gamma \to \infty$ the MCP tends to the Lasso. With the Lasso penalty the objective is convex for every $\lambda_1, \lambda_2 \ge 0$.

## Depends on

- [Lasso objective](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/lasso.md): the Lasso sparsity penalty
- [Residual sum of squares](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/rss.md): the least-squares loss of each trait

## Proof depends on

- [Convexity of the lasso objective](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/convex-on-lasso.md): convexity of the Lasso version
- [Weighted graph Laplacians and the Leroux precision matrix](../../../../Probability/linear-models-multivariate/gaussian-graphical-models/dot-product-laplacian-mul-vec-and-pos-de.md): the cross-trait penalty is a positive semidefinite Laplacian quadratic form, hence convex

## Expansion

The quadratic penalty is $\frac{\lambda_2}{2}\sum_j \beta_{\cdot j}^{\top}L_j\beta_{\cdot j}$ for the weighted graph Laplacian $L_j$ of the trait-similarity graph at SNP $j$ (plus a pull toward fixed anchors $\hat s_{mj}$), so it shrinks differences between a SNP's effects on related traits rather than the effects themselves; large $\lambda_2$ forces shared effects, which helps when traits share causal variants with similar effects. Because the squared loss and the Laplacian form are convex and the Lasso is convex, the Lasso version has no spurious local minima; the MCP trades this for less shrinkage bias on large effects. Tuning parameters are chosen by cross-validation on the primary trait only, using all secondary-trait individuals in every fold except those who also carry primary-trait data. In applications all weights were set to $a_{kk'j} = 1$.

## Sources

- W. Chung, J. Chen, C. Turman, S. Lindstrom, Z. Zhu, P.-R. Loh, P. Kraft and L. Liang, "Efficient cross-trait penalized regression increases prediction accuracy in large cohorts using secondary phenotypes", Nature Communications 10 (2019), Methods, "Prediction model", "Sparsity penalty" and "Cross-trait penalty", Eqs. (1)–(3), <https://doi.org/10.1038/s41467-019-08535-0>, PMCID PMC6361917.
