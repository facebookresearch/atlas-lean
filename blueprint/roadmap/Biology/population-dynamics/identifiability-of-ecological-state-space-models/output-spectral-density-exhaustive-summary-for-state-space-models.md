# Output spectral density exhaustive summary for linear stochastic state-space models

**Setting.** A linear time-invariant stochastic state-space model (SSM) in discrete time has a latent state $\mathbf{x}_t \in \mathbb{R}^N$ (e.g. log population sizes) and observations $\mathbf{y}_t$,
$$\mathbf{x}_{t+1} = \mathbf{A}\mathbf{x}_t + \mathbf{B}\mathbf{u}_t, \qquad \mathbf{y}_t = \mathbf{C}\mathbf{x}_t + \mathbf{D}\mathbf{u}_t,$$
driven by white noise $\mathbf{u}_t$ with covariance $\mathbf{Q}$ (process and observation noise), with all eigenvalues of $\mathbf{A}$ inside the unit disk; $\boldsymbol\theta$ collects the mean and variance parameters. With $s = e^{i\omega}$ and transfer function $\mathbf{H}_s(\boldsymbol\theta) = \mathbf{C}(s\mathbf{I} - \mathbf{A})^{-1}\mathbf{B} + \mathbf{D}$, the output spectral density is $\mathbf{S}(\boldsymbol\theta) = \mathbf{H}_s(\boldsymbol\theta)\,\mathbf{Q}\,\mathbf{H}_{1/s}(\boldsymbol\theta)^\top$. An *exhaustive summary* is a vector $\boldsymbol\kappa(\boldsymbol\theta)$ that determines the model; the model is *parameter redundant* (not locally identifiable) iff the derivative matrix $\partial\boldsymbol\kappa/\partial\boldsymbol\theta$ has rank smaller than the number of parameters.

**Theorem.** Each entry of the output spectral density is a rational function
$$[\mathbf{S}(\boldsymbol\theta)]_{ij} = \frac{\sum_{n=0}^{2N} a_n(\boldsymbol\theta)\,s^n}{\sum_{n=0}^{2N} b_n(\boldsymbol\theta)\,s^n},$$
with denominator proportional to $s^N\chi_{\mathbf A}(s)\chi_{\mathbf A}(1/s)$, and the non-constant coefficients $a_n, b_n$ form an exhaustive summary $\boldsymbol\kappa(\boldsymbol\theta)$ that accounts for both mean and noise parameters. The same holds in continuous time. Alternatively, the first $p$ Kalman-filter log-likelihood terms $l_t = \ln\det\mathbf{P}_t + \mathbf{z}_t^\top\mathbf{P}_t^{-1}\mathbf{z}_t$ form an exhaustive summary, and full rank of a model and of an extension's new parameters implies full rank of the extended model.

**Example (Gompertz model with observation error).** For $x_{t+1} = \rho x_t + \eta_t$, $y_t = x_t + \varepsilon_t$ with variances $\sigma^2_\eta, \sigma^2_\varepsilon$,
$$S(\boldsymbol\theta) = \frac{-\rho\sigma^2_\eta s^2 + (\rho^2\sigma^2_\eta + \sigma^2_\eta + \sigma^2_\varepsilon)s - \rho\sigma^2_\eta}{-\rho s^2 + (\rho^2 + 1)s - \rho}, \qquad \boldsymbol\kappa = \big(-\rho\sigma^2_\eta,\ \rho^2\sigma^2_\eta + \sigma^2_\eta + \sigma^2_\varepsilon,\ -\rho,\ \rho^2 + 1\big),$$
and $\partial\boldsymbol\kappa/\partial(\rho,\sigma^2_\eta,\sigma^2_\varepsilon)$ has rank $3$, so the model is not parameter redundant: estimation difficulties reported for it are practical, not structural. Across the stage-structured and multispecies models examined, redundancy appears only when some compartments are unobserved or parameters enter only as products (e.g. fecundity times juvenile survival).

## Depends on


## Expansion

The spectral density is the Fourier transform of the autocovariance of a stationary Gaussian output, so it determines the full second-order structure and hence the Gaussian likelihood; conversely a rational function in $s$ with fixed normalization is determined by its coefficients, which is why they form an exhaustive summary. Writing $\mathbf{H}_s = \mathbf{G}_s/\chi_{\mathbf A}(s)$ and multiplying by $\mathbf{H}_{1/s}^\top$ gives Laurent polynomials of degree $N$ in $s$ and $1/s$ over $\chi_{\mathbf A}(s)\chi_{\mathbf A}(1/s)$; multiplying through by $s^N$ yields the degree-$2N$ form. Expectation-based summaries miss the variance parameters, which the spectral density captures.

## Sources

- F. Barraquand and J. Gibaud, "Identifiability of linear stochastic state-space models with application to ecology", arXiv:2508.08714 (2025), Theorems 1–4, Corollary 5 and Section 4, <https://doi.org/10.48550/arXiv.2508.08714>.
