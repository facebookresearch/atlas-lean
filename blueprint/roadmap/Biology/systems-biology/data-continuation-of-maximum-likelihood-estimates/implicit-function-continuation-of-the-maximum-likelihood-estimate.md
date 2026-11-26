# Implicit-function continuation of the maximum likelihood estimate

Let a biological model be the ODE $\dot x=f(x,\theta)$, $x(0)=x_0(\theta)$, with $f$ continuously differentiable and parameters $\theta\in\Omega\subset\mathbb R^p$, and let $y_i(\theta)=h(x(t_i,\theta),\theta)$, $i=1,\dots,d$, be the model observables at the measurement times. For calibration data $\phi\in\mathbb R^d$ let $G(\theta,\phi)$ be a twice continuously differentiable objective, for example the Gaussian negative log-likelihood, which for a fixed known noise level is, up to constants and a positive factor, $G(\theta,\phi)=\sum_{i=1}^d\big(y_i(\theta)-\phi_i\big)^2$. The maximum likelihood estimate $\theta^*(\phi)$ minimises $G(\cdot,\phi)$ and therefore satisfies

$$D_\theta G(\theta^*,\phi)=0 .$$

**Result.** Let $\theta_0^*$ be a minimiser for data $\phi_0$ and suppose the Hessian $D^2_\theta G(\theta_0^*,\phi_0)$ is invertible. By the implicit function theorem there are a neighbourhood $S$ of $\phi_0$ and a continuously differentiable map $\Psi:S\to\mathbb R^p$ with $\Psi(\phi_0)=\theta_0^*$ and $D_\theta G(\Psi(\phi),\phi)=0$ for all $\phi\in S$, whose derivative is

$$D\Psi(\phi)=-\big[D^2_\theta G(\Psi(\phi),\phi)\big]^{-1}D^2_{\theta\phi}G(\Psi(\phi),\phi).$$

This gives the predictor $\Psi(\phi+\Delta\phi)=\Psi(\phi)+D\Psi(\phi)\Delta\phi+O(|\Delta\phi|^2)$ for how the estimate moves when the data change. For the least-squares objective, $\big(D^2_{\theta\phi}G\big)_{n,i}=-2\,\partial y_i/\partial\theta_n$, so the predictor needs only the output sensitivities and the Hessian. If the Hessian at $\theta_0^*$ is positive definite, it stays positive definite nearby, so $\Psi(\phi)$ is a strict local minimiser and not merely a stationary point. Where $D^2_\theta G$ is singular, as on the flat manifolds of structurally non-identifiable models, the continuation breaks down.

## Expansion

Apply the implicit function theorem to $F(\theta,\phi)=D_\theta G(\theta,\phi)$, whose Jacobian in $\theta$ is the Hessian; differentiating $F(\Psi(\phi),\phi)=0$ gives $D^2_\theta G\,D\Psi+D^2_{\theta\phi}G=0$. For least squares with residual $r=y(\theta)-\phi$ and sensitivity matrix $J=\partial y/\partial\theta$, $D_\theta G=2J^{\mathsf T}r$, $D^2_{\theta\phi}G=-2J^{\mathsf T}$, and at an exact fit $D^2_\theta G=2J^{\mathsf T}J$, so $D\Psi=(J^{\mathsf T}J)^{-1}J^{\mathsf T}$, the familiar linearised least-squares map. The predictor can be used to ask which additional or modified measurements would move a fitted parameter most, before running the experiment; in practice one solves the linear system $D^2_\theta G\,D\Psi=-D^2_{\theta\phi}G$ with finite-difference derivatives, at a cost of $2p(p+2)$ model simulations.

## Sources

- T. Cassidy, "A Continuation Technique for Maximum Likelihood Estimators in Biological Models", Bulletin of Mathematical Biology (2023), Methods, Eqs. (1)–(4), Theorem 1 (implicit function theorem, Eq. (5)), Eqs. (6)–(9) and the Numerical Implementation section, <https://doi.org/10.1007/s11538-023-01200-0>, PMCID PMC10471725.
