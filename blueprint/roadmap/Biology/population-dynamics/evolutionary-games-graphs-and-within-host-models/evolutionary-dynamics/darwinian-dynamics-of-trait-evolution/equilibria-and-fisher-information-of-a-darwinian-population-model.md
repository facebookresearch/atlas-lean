# Equilibria and information index of a Darwinian (evolutionary game) population model

**Model.** A population of density $x_t$ carries a mean trait $\theta_t$ that evolves by Darwinian (adaptive) dynamics:

$$x_{t+1} = x_t\,G(x_t, \theta_t), \qquad \theta_{t+1} = \theta_t + \sigma^2\,\partial_\theta \ln G(x_t, \theta_t),$$

with fitness generating function

$$G(x,\theta) = b(\theta)\,e^{-c_u(\theta)x}, \qquad b(\theta) = b_0\,e^{-\theta^2/(2w^2)}, \qquad c_u(\theta) = c_0\,e^{-\kappa(\theta - u)},$$

where $b_0 > 0$ is the maximal birth rate at the optimum trait $0$, $w > 0$ the width of the birth-rate profile, $c_0 > 0$ the competition coefficient, $\kappa > 0$ the trait sensitivity of competition, $u$ a reference trait and $\sigma^2 > 0$ the speed of evolution. Nontrivial equilibria $(x_*, \theta_*)$, $x_* \ne 0$, solve $G = 1$ and $\partial_\theta \ln G = 0$.

**Proposition (equilibria).** Let $\xi_1 = \frac{1}{\kappa^2} + 2w^2\ln b_0$.
1. If $\xi_1 < 0$ there is no nontrivial equilibrium.
2. If $\xi_1 = 0$ there is exactly one, with $\theta_* = -1/\kappa$.
3. If $\xi_1 > 0$ and $b_0 \ne 1$ there are two, with $\theta_{*\pm} = -\frac1\kappa \pm \sqrt{\xi_1}$. If $b_0 = 1$ (so $\xi_1 = 1/\kappa^2 > 0$) there is one, $\theta_{*-} = -2/\kappa$, since $\theta_{*+} = 0$ gives $x_* = 0$. The exception for $b_0 = 1$ corrects Proposition 3.3 of the source, which prints "If $\xi_1>0$, then the Darwinian system has two non trivial fixed points $(x_{*+},\theta_{*+})$ and $(x_{*-},\theta_{*-})$" with no exception.

In each case $x_* = \ln b(\theta_*)/c_u(\theta_*) = \theta_*\big/\big(\kappa w^2 c_u(\theta_*)\big)$, which is positive iff $\theta_* > 0$. Hence $\theta_{*-} < 0$ and the equilibrium with $\xi_1 = 0$ have $x_* < 0$, and a biologically meaningful equilibrium with $x_* > 0$ exists iff $b_0 > 1$; it is then unique, with $\theta_* = \theta_{*+}$.

**Definition and proposition (the source's information index).** Define

$$I(\theta) = \frac{1}{w^2} + \kappa^2\,\Gamma_u(\theta), \qquad \Gamma_u(\theta) = \frac{b(\theta)}{c_u(\theta)} = \frac{b_0}{c_0}\exp\Big(-\frac{\theta^2}{2w^2} + \kappa(\theta - u)\Big).$$

This is the expression $1/w^2 + \kappa^2c_u(\theta)\int_0^\infty xG(x,\theta)\,dx$ that the source calls the Fisher information of $G$; it is not the Fisher information of a probability law. Since $\int_0^\infty G(x,\theta)\,dx = \Gamma_u(\theta)$, $G(\cdot,\theta)$ is a density only where $\Gamma_u(\theta) = 1$; the normalized density $c_u(\theta)e^{-c_u(\theta)x}$ has Fisher information $\kappa^2$ (no maximizer), and $-\int_0^\infty \partial_\theta^2\ln G\cdot G\,dx = (1/w^2 + \kappa^2)\Gamma_u(\theta)$. The index $I$ is maximal at $\theta_{\max} = w^2\kappa$, with

$$I_{\max} = \frac{1}{w^2} + \kappa^2\,\frac{b_0}{c_0}\,e^{\frac12(w\kappa)^2 - \kappa u}.$$

For $n$ traits with $b(\Theta) = b_0\exp(-\sum_i \theta_i^2/(2w_i^2))$ and $c_{\mathbf U}(\Theta) = c_0\exp(-\sum_i \kappa_i(\theta_i - u_i))$, the corresponding index matrix is

$$I(\Theta) = \mathrm{diag}\big(w_1^{-2},\dots,w_n^{-2}\big) + \Gamma_{\mathbf U}(\Theta)\,\boldsymbol{\kappa}\boldsymbol{\kappa}^{\top}, \qquad \Gamma_{\mathbf U} = b/c_{\mathbf U},$$

which is positive definite.

## Proof sketch

From $G = 1$, $c_u(\theta)x = \ln b(\theta)$; from $\partial_\theta \ln G = -\theta/w^2 + \kappa c_u(\theta)x = 0$, $\kappa \ln b(\theta) = \theta/w^2$, i.e. $\theta^2 + \frac{2}{\kappa}\theta - 2w^2\ln b_0 = 0$, whose discriminant is $4\xi_1$. The index is the sum of a curvature term $1/w^2$ from the Gaussian birth profile and a term $\kappa^2 b/c_u$ from the trait dependence of competition. The normalized law has score $-\kappa + \kappa c_u x$, whose second moment is $\kappa^2$; for the unnormalized $G$, $-\partial_\theta^2\ln G = 1/w^2 + \kappa^2c_ux$, which integrates against $G$ to $(1/w^2+\kappa^2)\Gamma_u$. Maximising $\ln\Gamma_u = -\theta^2/(2w^2) + \kappa\theta + \text{const}$ gives $\theta_{\max}$. The multi-trait matrix is a diagonal plus rank-one update, so it is positive definite.

## Sources

- Eddy Kwessi, "Information Theory in a Darwinian Evolution Population Dynamics Model", *Symmetry* 16 (2024), 1522, <https://doi.org/10.3390/sym16111522>. Preprint version: arXiv:2403.05044 (2024), Section 3 (one-trait model, Theorem 3.1, Corollary 3.2, Proposition 3.3; multi-trait model, Theorem 3.6), <https://doi.org/10.48550/arXiv.2403.05044>.
