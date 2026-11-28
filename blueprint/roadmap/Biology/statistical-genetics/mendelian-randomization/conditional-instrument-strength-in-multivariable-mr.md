# Conditional instrument strength in multivariable Mendelian randomization

Consider multivariable MR with two exposures $X_1, X_2$ and $L$ independent variants. From summary data take SNP–exposure estimates $\hat\pi_{1j}, \hat\pi_{2j}$ with variances $\sigma_{1j}^2, \sigma_{2j}^2$ and covariance $\sigma_{12j}$. The two-sample MVMR model fits $\hat\Gamma_j = \beta_1\hat\pi_{1j} + \beta_2\hat\pi_{2j} + \epsilon_j$.

Separate strong $F$-statistics for $X_1$ and $X_2$ are necessary but not sufficient. The instruments must predict $X_1$ conditionally on their prediction of $X_2$, which fails if $(\pi_{1j})_j$ is proportional to $(\pi_{2j})_j$; then the model is under-identified. Nearly proportional effects give weak joint identification: the model is identified, as the source puts it, when "there are at least two elements of π1 and π2 … that differ", but the exposures are only "weakly predicted in a joint sense".

**Individual-level data.** Joint strength is measured by the Sanderson–Windmeijer **conditional $F$-statistic** $F_c$. Each exposure is regressed on the instrument-based predictions of the others, and $F_c$ tests whether the instruments still explain the residual variation. Values $F_c > 10$ for every exposure indicate adequate joint strength. Equivalently, under-identification for $X_1$ is tested as a Sargan over-identification test of $X_1 = \delta_0 + \delta X_2 + u_1$, with $X_2$ instrumented by the variants.

**Two-sample summary data.** Test under-identification for $X_1$ with the modified Cochran statistic

$$Q_{x1} = \sum_{j=1}^{L}\frac{(\hat\pi_{1j} - \hat\delta\,\hat\pi_{2j})^2}{\sigma_{x1j}^2}, \qquad \sigma_{x1j}^2 = \sigma_{1j}^2 + \hat\delta^2\sigma_{2j}^2 - 2\hat\delta\,\sigma_{12j},$$

with $\hat\delta$ an efficient estimate of $\delta$ in $\hat\pi_{1j} = \delta\hat\pi_{2j} + v_j$. Under the null that the instruments cannot predict both exposures, that is $\pi_{1j} = \delta\pi_{2j}$ for all $j$ (exact proportionality), $Q_{x1}$ is asymptotically $\chi^2_{L-1}$. Rejection ("heterogeneity is good") indicates that $X_1$ is identified. Swapping the roles of the exposures gives $Q_{x2}$, and both must exceed the critical value. If $\sigma_{12j}$ is unavailable it can be set to zero, which is exact when the two exposures come from separate samples and a good approximation when $\hat\delta\sigma_{12j}$ is small.

## Expansion

If $\pi_1 = \delta\pi_2$ exactly, the genetic predictions of $X_1$ and $X_2$ are collinear and $(\beta_1, \beta_2)$ is not identified. Then $\hat\pi_{1j} - \delta\hat\pi_{2j}$ is pure estimation noise with variance $\sigma_{x1j}^2$, and $Q_{x1}$ is a sum of $L$ squared standardized normals with one fitted parameter, hence $\chi^2_{L-1}$. Any real departure from proportionality adds a noncentral term and inflates $Q_{x1}$. In the summary-data setting $Q_{x1}$ thus plays the role of the over-identification test of the individual-level construction, whose equivalence with $F_c$ was shown separately. Unlike the single-exposure case, weak instruments in MVMR can bias each estimate in either direction.

## Sources

- E. Sanderson, G. Davey Smith, F. Windmeijer and J. Bowden, "An examination of multivariable Mendelian randomization in the single-sample and two-sample summary data settings", *International Journal of Epidemiology* 48(3) (2019), 713–727, <https://doi.org/10.1093/ije/dyy262> (PMC6734942), sections "Testing the assumptions of MVMR" (individual-level instrument strength) and "The two-sample summary data setting" (Equations 11–12, Table 2), and "Approximating $Q_{x1}$, $Q_{x2}$ and $Q_A$ with incomplete information".
