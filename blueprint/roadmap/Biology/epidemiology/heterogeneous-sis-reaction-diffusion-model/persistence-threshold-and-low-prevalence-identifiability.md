# Persistence threshold and low-prevalence identifiability of the SIS reaction-diffusion model

**Model.** On a bounded connected $C^2$ domain $\Omega \subset \mathbb{R}^d$, $1 \le d \le 3$, with Neumann boundary conditions,

$$\partial_t S - d_S\Delta S = -\beta(x)\frac{SI}{S+I} + \gamma(x)I, \qquad \partial_t I - d_I\Delta I = \beta(x)\frac{SI}{S+I} - \gamma(x)I,$$

with parameters $\theta = (\beta,\gamma,d_S,d_I)$, $\beta,\gamma \in C(\bar\Omega)$ and all four bounded above and below by positive constants, and $S_0 \ge s_* > 0$, $I_0 \ge 0$ bounded.

**Threshold.** Let $\mathcal{R}_0(\theta)$ be the variational basic reproduction number and $\lambda_*(\theta)$ the principal eigenvalue of $d_I\Delta + (\beta - \gamma)$ with Neumann conditions. Both are attained with strictly positive simple eigenfunctions, and

$$\mathcal{R}_0(\theta) > 1 \iff \lambda_*(\theta) > 0 .$$

**Theorem (low-prevalence expansion).** Replace $I_0$ by $\varepsilon i_0$ and let $i_\theta$ solve the linear problem $\partial_t i - d_I\Delta i = q_\theta i$, $q_\theta = \beta - \gamma$, $i(0) = i_0$. There is $C$, uniform in $\theta$ and $\varepsilon \in (0,1]$, with

$$\|I^\varepsilon_\theta\|_{L^\infty} \le C\varepsilon, \qquad \|I^\varepsilon_\theta - \varepsilon i_\theta\|_{C([0,T];L^2) \cap L^2(0,T;H^1)} \le C\varepsilon^2 ,$$

and the same $O(\varepsilon^2)$ bound in $L^\infty$. Hence two parameter sets with equal $\beta - \gamma$ and equal $d_I$ give early prevalence curves that differ only at order $\varepsilon^2$.

So early-epidemic data identify only the pair $(\beta - \gamma, d_I)$, which is exactly the pair that fixes $\lambda_*$ and hence persistence. The individual rates enter at second order through the saturation term $-\beta I^2/(S+I)$.

## Expansion

Standard incidence can be rewritten as $SI/(S+I) = I - I^2/(S+I)$, so the infected equation is linear with potential $\beta - \gamma$ plus a quadratic saturation term. Comparison gives $\|I\|_\infty \le \varepsilon e^{\bar\beta T}\|i_0\|_\infty$, and Duhamel's formula bounds the quadratic remainder by $C\varepsilon^2$. In Bayesian inversion with a Gaussian-type likelihood, the posterior is well defined and Lipschitz in the data, so uncertainty about the threshold sign can be quantified even while $\beta$ and $\gamma$ separately remain uncertain.

## Sources

- D.-L. Duong, "Bayesian inverse problems and epidemic-threshold uncertainty for a heterogeneous SIS reaction-diffusion model" (2026), Section 2 system, Theorems 1-2 and Theorems 4, 5 and 7, <https://doi.org/10.48550/arXiv.2611.14468>.
- L. J. S. Allen, B. M. Bolker, Y. Lou, A. L. Nevai, "Asymptotic profiles of the steady states for an SIS epidemic reaction-diffusion model", Discrete and Continuous Dynamical Systems 21 (2008), <https://doi.org/10.3934/dcds.2008.21.1>.
