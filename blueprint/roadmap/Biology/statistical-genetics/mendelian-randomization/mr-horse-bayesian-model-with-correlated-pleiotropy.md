# MR-Horse: Bayesian summary-data Mendelian randomization with correlated pleiotropy and a horseshoe prior

**Univariable model.** For $J$ genetic variants, let $\hat\beta_{Xj}$ and $\hat\beta_{Yj}$ be the estimated associations of variant $j$ with the exposure $X$ and the outcome $Y$, with known standard errors $\sigma_{Xj}$ and $\sigma_{Yj}$. With causal effect $\theta$, true variant–exposure effects $\beta_{Xj}$ and direct (pleiotropic) effects $\alpha_j$,

$$\hat\beta_{Yj}\sim N(\theta\beta_{Xj}+\alpha_j,\ \sigma_{Yj}^2),\qquad \hat\beta_{Xj}\sim N(\beta_{Xj},\ \sigma_{Xj}^2),\qquad j=1,\ldots,J.$$

The pair $(\beta_{Xj},\alpha_j)$ has the jointly normal prior

$$\begin{pmatrix}\beta_{Xj}\\ \alpha_j\end{pmatrix}\sim N\!\left(\begin{pmatrix}\mu\\0\end{pmatrix},\begin{pmatrix}s_X^2 & \rho_j s_X\phi_j\tau\\ \rho_j s_X\phi_j\tau & \phi_j^2\tau^2\end{pmatrix}\right),$$

with $\mu\sim N(0,1)$, $s_X^2\sim N^+(0,1)$, $\theta\sim N(0,1)$, local and global scales $\phi_j\sim\mathrm{Cauchy}^+(0,1)$ and $\tau\sim\mathrm{Cauchy}^+(0,1)$ (half-normal and half-Cauchy laws), and a correlation $\rho_j\in(-1,1)$, for example $\rho_j=2r_j-1$ with $r_j\sim\mathrm{Beta}(10,10)$. The causal estimate is the posterior mean of $\theta$, with an equal-tailed 95% credible interval.

Properties of the prior:

- Marginally $\alpha_j\mid\phi_j,\tau\sim N(0,\phi_j^2\tau^2)$ with half-Cauchy $\phi_j$ and $\tau$, so the $\alpha_j$ have a horseshoe prior: valid instruments ($\alpha_j=0$) are shrunk strongly toward $0$ while large pleiotropic effects escape shrinkage.
- The model covers valid instruments ($\alpha_j=0$), uncorrelated pleiotropy ($\alpha_j\ne0$, $\rho_j=0$, the InSIDE case) and correlated pleiotropy ($\alpha_j\ne0$, $\rho_j\ne0$, InSIDE violated). Conditioning the bivariate normal prior gives the moments displayed below.

$$\mathbb E[\alpha_j\mid\beta_{Xj}]=\frac{\rho_j\phi_j\tau}{s_X}(\beta_{Xj}-\mu),\qquad \operatorname{Var}(\alpha_j\mid\beta_{Xj})=(1-\rho_j^2)\phi_j^2\tau^2$$

So with $\rho_j\ne0$ the pleiotropic effect co-varies with instrument strength. Further:

- The model uses $\sigma_{Xj}$, so it accounts for uncertainty in the variant–exposure associations (weak instruments), unlike the inverse-variance-weighted model $\hat\beta_{Yj}\sim N(\theta\hat\beta_{Xj},\sigma_{Yj}^2)$.

**Multivariable model (MVMR-Horse).** For $K$ exposures, let $\beta_{Xj\cdot}\in\mathbb R^K$ with estimate $\hat\beta_{Xj\cdot}$ of known covariance $\Sigma_{Xj}$, and $\theta\in\mathbb R^K$ the direct causal effects:

$$\hat\beta_{Yj}\sim N(\theta^\top\beta_{Xj\cdot}+\alpha_j,\ \sigma_{Yj}^2),\qquad \hat\beta_{Xj\cdot}\sim N(\beta_{Xj\cdot},\ \Sigma_{Xj}),$$

$$\begin{pmatrix}\beta_{Xj\cdot}\\ \alpha_j\end{pmatrix}\sim N\!\left(\begin{pmatrix}\mu\\0\end{pmatrix},\begin{pmatrix}V_X & \operatorname{diag}(V_X)^{1/2}\rho_j\phi_j\tau\\ \rho_j\phi_j\tau\,\{\operatorname{diag}(V_X)^{1/2}\}^\top & \phi_j^2\tau^2\end{pmatrix}\right),$$

where $V_X=\operatorname{diag}(v_1,\ldots,v_K)$ and $\operatorname{diag}(V_X)^{1/2}$ denotes the vector $(v_1^{1/2},\ldots,v_K^{1/2})^\top$, with priors $\mu\sim N(0,I_K)$, $(v_1,\ldots,v_K)\sim N^+(0,I_K)$ (the analogue of $s_X^2\sim N^+(0,1)$), $\theta_k\sim N(0,1)$, the same half-Cauchy $\phi_j$ and $\tau$, and $\rho_j$ as above.

## Depends on

- [Inverse-variance-weighted estimator](ivw.md)
- [InSIDE identity for MR-Egger](egger-slope-eq-of-inside.md)
- [Directional pleiotropy biases the IVW estimator](ivw-of-pleiotropy.md)

## Expansion

- The data model is the same general model of instrument invalidity used by constrained-maximum-likelihood MR: each variant may be valid, pleiotropic independently of its exposure effect, or pleiotropic through a confounder (which induces correlation between $\beta_{Xj}$ and $\alpha_j$; population structure acts the same way).
- Writing the covariance as $\begin{pmatrix}s_X^2&c\\c&\phi_j^2\tau^2\end{pmatrix}$ with $c=\rho_js_X\phi_j\tau$, it is positive definite for $|\rho_j|<1$, and the conditional moments follow from the standard formula $\mathbb E[\alpha\mid\beta]=c\,s_X^{-2}(\beta-\mu)$, $\operatorname{Var}(\alpha\mid\beta)=\phi_j^2\tau^2-c^2s_X^{-2}$.
- The model ignores sample overlap and linkage disequilibrium between variants; both can be added by correlating $\hat\beta_{Yj}$ with $\hat\beta_{Xj}$ or across variants. Posterior sampling is by Markov chain Monte Carlo.

## Sources

- A. J. Grant, S. Burgess, *A Bayesian approach to Mendelian randomization using summary statistics in the univariable and multivariable settings with correlated pleiotropy*, American Journal of Human Genetics 111 (2024), <https://doi.org/10.1016/j.ajhg.2023.12.002>, PMCID PMC10806746 (Methods: Univariable Mendelian randomization; Multivariable Mendelian randomization).
