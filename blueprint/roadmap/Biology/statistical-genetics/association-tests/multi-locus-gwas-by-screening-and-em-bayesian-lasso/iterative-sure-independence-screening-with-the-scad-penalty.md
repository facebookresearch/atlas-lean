# Iterative sure independence screening with the SCAD penalty

Let a quantitative trait $y \in \mathbb{R}^n$ follow, after ordinary-least-squares correction for fixed covariates such as population structure, the linear model

$$y = \mu + \sum_{i=1}^{p} X_i \beta_i + \varepsilon, \qquad \varepsilon \sim \mathrm{MVN}_n(0, \sigma^2 I),$$

with $X_i \in \mathbb{R}^n$ the genotype vector of SNP $i$ and $p \gg n$. Sure independence screening keeps only the SNPs whose marginal correlation with $y$ is significant; the survivors are then fitted by penalized least squares

$$\hat\beta = \arg\min_{\beta} \Bigl\{ \sum_{k=1}^{n} \Bigl(y_k - \sum_{j} X_{kj} \beta_j\Bigr)^2 + \sum_{j} \rho_{\lambda,\gamma}(|\beta_j|) \Bigr\}$$

with the smoothly clipped absolute deviation (SCAD) penalty, defined for $\lambda > 0$, $\gamma > 2$ and $t \ge 0$ by

$$\rho_{\lambda,\gamma}(t) = \begin{cases} \lambda t, & t \le \lambda, \\[2pt] \dfrac{\gamma \lambda t - \tfrac12 (t^2 + \lambda^2)}{\gamma - 1}, & \lambda < t \le \gamma \lambda, \\[6pt] \dfrac{\lambda^2 (\gamma + 1)}{2}, & t > \gamma\lambda. \end{cases}$$

Iterated screening repeats the marginal step conditionally on the SNPs already selected, so that SNPs marginally uncorrelated with $y$ but jointly relevant can enter. The union of selected SNPs is passed to a multi-locus mixed-model estimator for effect estimation and testing.

## Expansion

The SCAD penalty is continuous and continuously differentiable on $(0, \infty)$, with derivative $\rho'(t) = \lambda$ for $t \le \lambda$, $(\gamma\lambda - t)/(\gamma - 1)$ on $(\lambda, \gamma\lambda]$, and $0$ beyond, so it behaves like the lasso near zero (producing exact zeros) but stops shrinking large effects, which removes the lasso's bias on strong QTN and gives the oracle property; $\gamma = 3.7$ is the usual default, and $\gamma \to \infty$ recovers the $L_1$ penalty. The selected set is deliberately liberal, so a later likelihood-based significance test is needed to control false detections. The screening reduces $p$ from hundreds of thousands to a size that a mixed-model EM can handle.

## Sources

- Tamba CL, Ni YL, Zhang YM. Iterative sure independence screening EM-Bayesian LASSO algorithm for multi-locus genome-wide association studies. *PLoS Computational Biology* (2017), Methods, "Genetic model", "SCAD" (equations (1)–(4)) and "Iterative Sure Independence Screening-EM Bayesian LASSO". DOI <https://doi.org/10.1371/journal.pcbi.1005357>. PMCID PMC5308866.
- Fan J, Li R. Variable selection via nonconcave penalized likelihood and its oracle properties. *Journal of the American Statistical Association* 96:1348–1360 (2001). DOI <https://doi.org/10.1198/016214501753382273>.
