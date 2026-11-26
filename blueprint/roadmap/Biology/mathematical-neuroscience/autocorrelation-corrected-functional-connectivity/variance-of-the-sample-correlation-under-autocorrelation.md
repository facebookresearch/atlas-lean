# Variance of the sample correlation under autocorrelation

**Setting.** Let $X = (x_1,\dots,x_N)$ and $Y = (y_1, \dots, y_N)$ be jointly Gaussian, mean-zero, unit-variance stationary time series with Toeplitz autocorrelation matrices $\Sigma_X$, $\Sigma_Y$ (entries $\rho_{XX,k}$, $\rho_{YY,k}$ at lag $k = i - j$) and cross-correlation matrix $\Sigma_{XY} = \Sigma_{YX}^{\mathsf T}$ with entries $\rho_{XY,k}$ (not symmetric in $k$). The target is the lag-0 correlation $\rho = \rho_{XY,0}$, estimated by $\hat\rho = X^{\mathsf T}Y/\sqrt{X^{\mathsf T}X\, Y^{\mathsf T}Y}$.

**Quadratic-form lemma.** If $G \sim N(0, \Phi)$ and $A, B$ are fixed symmetric matrices, then $\mathrm{Cov}(G^{\mathsf T}AG, G^{\mathsf T}BG) = 2\,\mathrm{tr}(\Phi A \Phi B)$. With $G = (X, Y)$, the inner products $X^{\mathsf T}X$, $Y^{\mathsf T}Y$, $X^{\mathsf T}Y$ are quadratic forms in $G$.

**Variance (xDF).** Propagating these moments through $\hat\rho$ gives

$$V(\hat\rho) = N^{-2}\Big[\tfrac{\rho^2}{2}\mathrm{tr}(\Sigma_X^2) + \tfrac{\rho^2}{2}\mathrm{tr}(\Sigma_Y^2) + \rho^2\,\mathrm{tr}(\Sigma_{YX}\Sigma_{XY}) + \mathrm{tr}(\Sigma_{XY}^2) + \mathrm{tr}(\Sigma_X\Sigma_Y) - \rho\,\mathrm{tr}(\Sigma_X\Sigma_{XY}) - \rho\,\mathrm{tr}(\Sigma_{YX}\Sigma_X) - \rho\,\mathrm{tr}(\Sigma_{XY}\Sigma_Y) - \rho\,\mathrm{tr}(\Sigma_Y\Sigma_{YX})\Big],$$

which for stationary series can be rewritten as weighted sums over lags of products of auto- and cross-correlations.

**Special cases.**
1. White but correlated series ($\Sigma_X = \Sigma_Y = I$, $\Sigma_{XY} = \rho I$): $V(\hat\rho) = (1-\rho^2)^2/N$, the classical result.
2. Autocorrelated but mutually uncorrelated series ($\Sigma_{XY} = 0$): $V(\hat\rho) = N^{-2}\mathrm{tr}(\Sigma_X\Sigma_Y) = N^{-2}\big(N + 2\sum_{k=1}^{N-1}(N-k)\rho_{XX,k}\rho_{YY,k}\big)$, the Bayley–Hammersley variance inflation.

**Effective degrees of freedom.** Writing $V(\hat\rho) = (1 - \rho^2)^2/\hat N$ defines an effective sample size $\hat N$. Under $\rho = 0$ it reduces to Quenouille's $\hat N = N\big(\sum_{k=-\infty}^{\infty}\rho_{XX,k}\rho_{YY,k}\big)^{-1}$, and for two AR(1) series with lag-one coefficients $\phi_X, \phi_Y$ to Bartlett's $\hat N = N\,\frac{1 - \phi_X\phi_Y}{1 + \phi_X\phi_Y}$.

## Expansion

Substituting case 1 into the trace formula gives $N(\rho^2 + \rho^4 + \rho^2 + 1 - 4\rho^2)/N^2 = (1-\rho^2)^2/N$, a useful check on the signs. Positive autocorrelation in both series inflates the variance through the $\mathrm{tr}(\Sigma_X\Sigma_Y)$ term, so treating $N$ time points as independent overstates the evidence for a connection, and Fisher's $z$-transform no longer stabilizes the variance. Unlike global corrections that use one autocorrelation for all nodes, the formula is evaluated per pair from estimated (regularized, truncated) autocorrelation and cross-correlation functions; in resting-state fMRI the correction varies strongly across region pairs with region size and location, and applying it changes thresholded network topology.

## Sources

- S. Afyouni, S. M. Smith, T. E. Nichols, "Effective degrees of freedom of the Pearson's correlation coefficient under autocorrelation", NeuroImage 199:609–625 (2019), Eqs 1–7 and Appendix A Theorem 1, <https://doi.org/10.1016/j.neuroimage.2019.05.011>, PMCID PMC6693558.
