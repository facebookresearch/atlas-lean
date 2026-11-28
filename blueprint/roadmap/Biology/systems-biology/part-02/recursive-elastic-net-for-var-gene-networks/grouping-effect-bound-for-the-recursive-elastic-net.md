# Grouping-effect bound for the recursive elastic net

**Setting.** In one regression $\mathbf z = X\boldsymbol\beta + \mathbf e$ of the recursive elastic net, let the response $\mathbf z \in \mathbb R^{n-1}$ be centered and the columns $\mathbf x_1,\dots,\mathbf x_m$ of $X$ standardized to unit Euclidean norm, so that $\rho = \mathbf x_i'\mathbf x_j$ is the sample correlation of covariates $i$ and $j$ and $\|\mathbf x_i - \mathbf x_j\|_2 = \sqrt{2(1-\rho)}$. Fix $\lambda_1 \ge 0$, $\lambda_2 > 0$ and the $l$-th iteration weights $w_k^{(l)} = 1/(|\hat\beta_k^{(l-1)}| + \delta)$, and let $\hat{\boldsymbol\beta}^{(l)}$ be the weighted elastic net minimizer. Define the normalized coefficient gap

$$D_{i,j}^{(l)} = \frac{1}{\|\mathbf z\|_1}\,\big|\hat\beta_i^{(l)} - \hat\beta_j^{(l)}\big|, \qquad \|\mathbf z\|_1 = \sum_{i}|z_i|.$$

**Lemma (identical covariates).** If $\mathbf x_i = \mathbf x_j$ then $\hat\beta_i^{(l)} = \hat\beta_j^{(l)}$ for every $\lambda_2 > 0$ (quoted from the elastic-net theory of Zou and Hastie; it requires equal weights on the two coordinates, which the recursive weights inherit at every step if they start equal).

**Theorem (grouping bound).** If $\hat\beta_i^{(l)}\hat\beta_j^{(l)} > 0$, then

$$D_{i,j}^{(l)} \le \frac{1}{\lambda_2}\Big\{\sqrt{2(1-\rho)} + \frac{\lambda_1}{\|\mathbf z\|_1}\,\big|w_i^{(l)} - w_j^{(l)}\big|\Big\}.$$

If moreover $1/x$ is $1$-Lipschitz on the relevant range, i.e. $(|\hat\beta_i^{(l-1)}| + \delta)(|\hat\beta_j^{(l-1)}| + \delta) \ge 1$, then

$$D_{i,j}^{(l)} \le \frac{1}{\lambda_2}\Big\{\sqrt{2(1-\rho)} + \lambda_1 D_{i,j}^{(l-1)}\Big\}.$$

So highly correlated covariates ($\rho \approx 1$) whose previous coefficients were nearly equal keep nearly equal coefficients, unlike the lasso, which tends to select only one of a correlated group.

## Expansion

For coordinates with $\hat\beta_i^{(l)}, \hat\beta_j^{(l)} \ne 0$ of the same sign, the stationarity conditions of the strictly convex objective are

$$-\mathbf x_i'(\mathbf z - X\hat{\boldsymbol\beta}^{(l)}) + \lambda_1 w_i^{(l)}\operatorname{sgn}(\hat\beta_i^{(l)}) + \lambda_2\hat\beta_i^{(l)} = 0,$$

and the same for $j$. Subtracting,

$$\lambda_2\big|\hat\beta_i^{(l)} - \hat\beta_j^{(l)}\big| \le \|\mathbf x_i - \mathbf x_j\|_2\,\|\mathbf z - X\hat{\boldsymbol\beta}^{(l)}\|_2 + \lambda_1\big|w_i^{(l)} - w_j^{(l)}\big|.$$

Comparing the objective at $\hat{\boldsymbol\beta}^{(l)}$ with its value at $\boldsymbol\beta = \mathbf 0$ gives $\|\mathbf z - X\hat{\boldsymbol\beta}^{(l)}\|_2 \le \|\mathbf z\|_2 \le \|\mathbf z\|_1$, and dividing by $\lambda_2\|\mathbf z\|_1$ yields the first bound. For the second, $|w_i^{(l)} - w_j^{(l)}| = \big||\hat\beta_i^{(l-1)}| - |\hat\beta_j^{(l-1)}|\big| / \big((|\hat\beta_i^{(l-1)}|+\delta)(|\hat\beta_j^{(l-1)}|+\delta)\big)$, which is at most $|\hat\beta_i^{(l-1)} - \hat\beta_j^{(l-1)}|$ when the denominator is at least $1$. The source states the recursive bound without that condition, invoking a Lipschitz property of $x\mapsto 1/x$ that holds only on $[1,\infty)$; for small coefficients and $\delta = 10^{-5}$ the weight gap can be far larger, and only the first bound is unconditional.

## Depends on

- [Recursive elastic net for VAR gene network inference](recursive-elastic-net-for-var-gene-network-inference.md)

## Sources

- T. Shimamura, S. Imoto, R. Yamaguchi, A. Fujita, M. Nagasaki, S. Miyano, "Recursive regularization for inferring gene networks from time-course gene expression profiles", BMC Systems Biology 3 (2009) 41, section Grouping Effect: Lemma 1, Theorem 1, Equations (12)-(13); Appendix: Equations (21)-(27), <https://doi.org/10.1186/1752-0509-3-41>, PMCID PMC2686685.
- H. Zou, T. Hastie, "Regularization and variable selection via the elastic net", Journal of the Royal Statistical Society, Series B 67 (2005) 301-320, <https://doi.org/10.1111/j.1467-9868.2005.00503.x>.
