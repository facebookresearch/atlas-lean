# Conditional ball covariance screening for confounder selection

**Variables.** Observe i.i.d. copies of $(X, D, Y)$ with binary treatment $D$, outcome $Y$ and ultra-high-dimensional covariates $X = (X^{(1)},\dots,X^{(p)})$, $p = O\{\exp(n^\iota)\}$ for some $\iota > 0$. Covariates split into confounders $X^C$ (affect $D$ and $Y$), precision variables $X^P$ (affect only $Y$), instruments $X^I$ (affect only $D$) and null variables $X^N$. The target adjustment set for the doubly robust estimator of $\Delta = \mathbb E\{Y(1) - Y(0)\}$ is $\mathcal A = C \cup P$: instruments are excluded because restricting them lowers the semiparametric efficiency bound (Hahn 2004), precision variables are kept.

**Ball covariance.** For random elements $X, Y$ with joint law $\theta$ and marginals $\mu,\nu$ on metric spaces, with closed balls $\bar B_\rho(x_1,x_2) = \{x : \rho(x,x_1) \le \rho(x_1,x_2)\}$,
$$\mathrm{BCov}^2(X,Y) = \int \big(\theta - \mu\otimes\nu\big)^2\big\{\bar B_\rho(x_1,x_2)\times\bar B_\xi(y_1,y_2)\big\}\,\theta(dx_1,dy_1)\,\theta(dx_2,dy_2),$$
and $\mathrm{BCov}(X,Y) = 0$ iff $X \perp\!\!\!\perp Y$ (Pan et al.). With $\omega = P(D=1)$ and $(X^{(d)},Y^{(d)}) \overset{d}{=} (X,Y \mid D = d)$, the **conditional ball covariance** is
$$\mathrm{BCov}^2(X,Y\mid D) = \omega\,\mathrm{BCov}^2(X^{(1)},Y^{(1)}) + (1-\omega)\,\mathrm{BCov}^2(X^{(0)},Y^{(0)}),$$
and $\mathrm{BCov}(X,Y\mid D) = 0 \iff X \perp\!\!\!\perp Y \mid D$. Its empirical version $\hat\rho_j = \mathrm{BCov}_n^2(X^{(j)},Y\mid D)$ combines the within-arm sample ball covariances with weight $\hat\omega = n_1/n$.

**Screening rule.** Keep the $q$ covariates with the largest $\hat\rho_j$, giving a set $K$.

**Theorem (sure screening).** Let $\rho_j = \mathrm{BCov}^2(X^{(j)},Y\mid D)$ and $W = \{j : \rho_j = 0\}$ with $|W^c| \le q$. Assume (A1) $\min_{j \in C\cup P}\rho_j \ge 2cn^{-\kappa}$ for constants $c > 0$, $0 \le \kappa < 1/2$, and (A2) $\log p = o(n^{1-2\kappa})$. Then
$$P\Big(\max_{j\in W}\hat\rho_j < \min_{j\in\mathcal A}\hat\rho_j\Big) \to 1, \qquad P\big((X^C\cup X^P) \subseteq K\big) \to 1.$$

In a faithful causal DAG, $X^N \perp\!\!\!\perp Y \mid D$ while $X^I$ depends on $Y$ given $D$ only through collider bias, so conditioning on $D$ makes instruments weak and screenable. A second stage fits adaptive-lasso outcome and propensity models on $K$, selects $\mathcal A$ consistently, and plugs the selected models into the augmented inverse-probability-weighted estimator, which is consistent if either model is correct.

## Depends on

- [Riesz representer and the doubly robust moment of a linear functional](riesz-representer-and-doubly-robust-moment.md)

## Expansion

The empirical conditional ball covariance is a weighted combination of U-/V-statistics with bounded kernels, so exponential concentration gives $\max_j|\hat\rho_j - \rho_j| = o_p(n^{-\kappa})$ under (A2) via a union bound over $p$ covariates; the gap $2cn^{-\kappa}$ in (A1) then separates the signal set from $W$. Being model-free in $X$, the screen does not require a correctly specified outcome model, which preserves the double robustness of the final estimator.

## Sources

- Dingke Tang, Dehan Kong and Wenliang Pan, "Ultra-High Dimensional Variable Selection for Doubly Robust Causal Inference", Biometrics (2022), <https://doi.org/10.1111/biom.13625>. arXiv:2007.14190. Definitions 1–4; Propositions 1–3; Section 3.1; Theorem 1 and Theorem 2.
