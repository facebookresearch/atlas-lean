# Common bias of preliminary log-linear estimators of differential abundance

**Model.** For samples $i = 1, \dots, n$ with covariates $x_i \in \mathbb{R}^{p}$ (design matrix $X$ with an
intercept column) and taxa $j = 1, \dots, d$, let $o_{ij}$ be the log observed count. Sequencing
observes only a sample-specific fraction of the absolute abundance and taxa are detected with
taxon-specific efficiency, so

$$o_{ij} = s_i + c_j + b_j^{\mathsf{T}} x_i + e_{ij}, \qquad E(e_{ij}) = 0, \quad \operatorname{Var}(e_{ij}) = \sigma^2_{ij},$$

with $s_i$ the log sampling fraction, $c_j$ the log efficiency and $b_j$ the log fold changes in absolute
abundance. Centering over samples removes $c_j$:
$y_{ij} = o_{ij} - \bar{o}_{\cdot j} = \theta_i + \beta_j^{\mathsf{T}} x_i + \epsilon_{ij}$, with
$\theta_i = s_i - \bar{s}$ and $\beta_{jk} = b_{jk}$ for $k \ge 1$. Here $\beta_j$ is not identifiable without
the nuisance $\theta$.

**Preliminary estimators.** Alternate $\theta \leftarrow \frac{1}{d} \sum_j (y_j - X\beta_j)$ and
$\beta_j \leftarrow (X^{\mathsf{T}}X)^{-1} X^{\mathsf{T}} (y_j - \theta)$ until convergence, giving
$\theta^{*}, \beta_j^{*}$.

**Proposition.** With $P = X(X^{\mathsf{T}}X)^{-1}X^{\mathsf{T}}$,
$(I - P)\bigl(E(\theta^{*}) - \theta\bigr) = 0$, so $E(\theta^{*}) = \theta - X\delta$ for a single vector
$\delta \in \mathbb{R}^{p}$ and

$$E(\beta_j^{*}) = \beta_j + \delta \quad \text{for every taxon } j.$$

Moreover, as $n \to \infty$ with $d$ fixed,
$\hat{\Sigma}_j^{-1/2}\bigl(\beta_j^{*} - (\beta_j + \delta)\bigr) \to N(0, I)$ with the sandwich estimator
$\hat{\Sigma}_j = (X^{\mathsf{T}}X)^{-1} \sum_i (y_{ij} - \theta^{*}_i - \beta_j^{*\mathsf{T}} x_i)^2 x_i x_i^{\mathsf{T}} (X^{\mathsf{T}}X)^{-1}$, and
$\beta_j^{*} \to \beta_j + \delta$ in probability.

**Bias estimation.** Because the bias is shared by all taxa, for each covariate $k$ the coefficients
$\beta^{*}_{jk}$ follow a three-component Gaussian mixture: null taxa ($\beta_{jk} = 0$) centered at $\delta_k$,
decreasing taxa at $\delta_k + l_1$ ($l_1 < 0$), increasing taxa at $\delta_k + l_2$ ($l_2 > 0$), with variances
$\nu_{j0} \le \nu_{j1}, \nu_{j2}$; the EM algorithm estimates $\delta_k$, and tests of $A\beta_j = A\beta_j^{0}$ use
the bias-corrected $\beta_j^{*} - \hat{\delta}$.

## Expansion

Since $\beta_j^{*}$ is the least squares fit to $y_j - \theta^{*}$, any error in $\theta^{*}$ lying in the
column space of $X$ is absorbed identically by every taxon's coefficients; the fixed-point equation
$\theta^{*} = (I - P)\theta + P\theta^{*} + \frac{1}{d}\sum_j (I - P) y^{\mathrm{crt}}_j$ shows that only such
an error survives in expectation. Unequal sampling fractions are therefore a compositional effect
that shifts all log fold changes by the same amount, and pooling across taxa, under the assumption
that a component of taxa is null, recovers it. Without correction, tests of differential abundance
are centered away from zero under the null and lose false discovery control.

## Sources

- H. Lin, S. D. Peddada, "Multigroup analysis of compositions of microbiomes with covariate
  adjustments and repeated measures", Nature Methods 21 (2024), Methods, Eqs. 3-14, Algorithm 1 and
  Lemma 1, <https://doi.org/10.1038/s41592-023-02092-7> (PMC10776411).
