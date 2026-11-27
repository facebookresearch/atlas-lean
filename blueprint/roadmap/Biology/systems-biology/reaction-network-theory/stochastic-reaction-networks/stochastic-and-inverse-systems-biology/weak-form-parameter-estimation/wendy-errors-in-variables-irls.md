# WENDy covariance correction and iteratively reweighted least squares

In the [weak-form regression](weak-form-ode-regression.md), vectorize the parameters $\mathbf w = \operatorname{vec}(W) \in \mathbb R^{Jd}$ and set $\mathbf G = I_d \otimes (\phi\,\Theta(U))$, $\mathbf b = -\operatorname{vec}(\dot\phi\, U)$. Suppose $U = u^\star + \varepsilon$ with i.i.d. $N(0, \sigma^2)$ entries of $\varepsilon$, and let $\mathbf w^\star$, $\mathbf G^\star$, $\mathbf b^\star$ be the noise-free quantities. The residual decomposes as

$$\mathbf r(U, \mathbf w) = \mathbf G\mathbf w - \mathbf b = \underbrace{(\mathbf G - \mathbf G^\star)\mathbf w}_{e_\Theta} + \underbrace{\mathbf G^\star(\mathbf w - \mathbf w^\star)}_{r_0} + \underbrace{(\mathbf G^\star\mathbf w^\star - \mathbf b^\star)}_{e_{\mathrm{int}}} - \mathbf b^{\varepsilon},$$

and to first order in $\varepsilon$, $e_\Theta - \mathbf b^{\varepsilon} = \mathbf L_{\mathbf w}\operatorname{vec}(\varepsilon) + \mathbf h(U, \mathbf w, \varepsilon)$ with higher-order remainder $\mathbf h$ and

$$\mathbf L_{\mathbf w} = \bigl[\operatorname{mat}(\mathbf w)^\top \otimes \phi\bigr]\nabla\Theta\, \mathbf K + \bigl[I_d \otimes \dot\phi\bigr],$$

where $\nabla\Theta$ stacks the feature gradients $\nabla f_j(U_m)$ and $\mathbf K$ is the commutation matrix, $\mathbf K\operatorname{vec}(\varepsilon) = \operatorname{vec}(\varepsilon^\top)$. Hence, approximately, $\mathbf r - (r_0 + e_{\mathrm{int}}) \sim N(0, \sigma^2 \mathbf L_{\mathbf w}\mathbf L_{\mathbf w}^\top)$, and at $\mathbf w = \mathbf w^\star$ with negligible quadrature error, $\mathbf G\mathbf w^\star - \mathbf b \sim N(0, \sigma^2\mathbf L_{\mathbf w^\star}\mathbf L_{\mathbf w^\star}^\top)$.

**WENDy (IRLS).** Starting from OLS, iterate

$$\mathbf C^{(n)} = (1 - \alpha)\mathbf L_{\mathbf w^{(n)}}\mathbf L_{\mathbf w^{(n)}}^\top + \alpha I, \qquad \mathbf w^{(n+1)} = \arg\min_{\mathbf w} (\mathbf G\mathbf w - \mathbf b)^\top (\mathbf C^{(n)})^{-1}(\mathbf G\mathbf w - \mathbf b),$$

with a small relaxation $\alpha \in [0, 1]$ ($\alpha = 1$ is OLS). Assume $\operatorname{rank}(\phi\,\Theta(U)) = J$, so $\mathbf G$ has full column rank $Jd$ and $\mathbf G^\top\mathbf G$ is invertible, and that each $\mathbf C^{(n)}$ is invertible: this holds for every $\alpha \in (0, 1]$, since then $\mathbf C^{(n)} \succeq \alpha I \succ 0$, while at $\alpha = 0$ it requires $\mathbf L_{\mathbf w^{(n)}}$ to have full row rank. Under these assumptions each weighted least-squares step has a unique minimiser. At convergence, $\mathbf b \approx N(\mathbf G\hat{\mathbf w}, \hat\sigma^2\hat{\mathbf C})$ and the parameter covariance is estimated by

$$\mathbf S = \hat\sigma^2\, (\mathbf G^\top\mathbf G)^{-1}\mathbf G^\top\, \hat{\mathbf C}\, \mathbf G(\mathbf G^\top\mathbf G)^{-1},$$

where $\hat{\mathbf C}$ is the limiting covariance, assumed invertible as above (take $\alpha > 0$, or $\mathbf L_{\hat{\mathbf w}}$ of full row rank at $\alpha = 0$); this gives standard errors and correlations of the estimates.

## Expansion

$e_\Theta$ is $[I_d \otimes \phi(\Theta(U) - \Theta(U - \varepsilon))]\mathbf w$; a first-order Taylor expansion of each feature in the data gives the $\nabla\Theta$ term, and $\mathbf b^\varepsilon = -\operatorname{vec}(\dot\phi\,\varepsilon)$ gives the $I_d \otimes \dot\phi$ term. The covariance depends on $\mathbf w$, so generalized least squares is iterated with the covariance re-evaluated at the current estimate. The first-order approximation is good when the features are close to linear on the scale of the noise; for strongly nonlinear features and large noise the improvement over OLS is limited.

## Depends on

- [Weak-form linear regression for ODE parameters](weak-form-ode-regression.md)

## Sources

- D. M. Bortz, D. A. Messenger and V. Dukić, "Direct estimation of parameters in ODE models using WENDy: weak-form estimation of nonlinear dynamics", *Bulletin of Mathematical Biology* 85 (2023), <https://doi.org/10.1007/s11538-023-01208-6> (PMC10556152). Section 2.2, equations (8)–(15) and Algorithm 2.
