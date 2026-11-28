# Obstacle-induced short-range attraction between self-propelled particles

In one space dimension, with no obstacle noise and the obstacle density kept to first order in $\gamma$, the SPP density $\rho_g(x,t)$ obeys a nonlocal aggregation–diffusion equation:

$$
\partial_t \rho_g + c_1 \partial_x \rho_g = \frac{1}{\zeta}\,\partial_x\Big(\rho_g\, \partial_x\big(\mu\rho_g + \tfrac{\gamma}{\eta}\, W * \rho_g\big)\Big),
\qquad
W = \phi' * \phi' .
$$

Here $\phi$ is the microscopic SPP–obstacle interaction potential, $\mu > 0$ is the SPP self-repulsion, $c_1 > 0$ is the self-propulsion speed, and $\zeta, \eta > 0$ are frictions. So $W$ acts as an effective SPP–SPP interaction potential mediated by the obstacles.

**Lemma 3.** Let $\phi$ be even, and write $\phi'(x) = \varphi(|x|)\operatorname{sign}(x)$ with $\varphi(0) := \lim_{r \to 0^+}\varphi(r) \ne 0$. Assume $\varphi$ is continuous with bounded derivative on $[0, \infty)$, supported in $[0, r_I]$, and that $\varphi$ and $\varphi'$ have constant opposite signs on the support. Then:

1. $W$ is even, continuous on $\mathbb{R}$, continuously differentiable on $\mathbb{R} \setminus \{0\}$, and supported in $[-2r_I, 2r_I]$.
2. $\lim_{x \to 0^+} W'(x) = 2\varphi(0)^2 > 0$, so $W$ is attractive at short distances.
3. $W'(x) < 0$ on $(r_I, 2r_I)$, so $W$ is repulsive at intermediate distances.

The conclusions are unchanged under $\phi \mapsto -\phi$, since $W$ is quadratic in $\phi$. Repulsive and attractive SPP–obstacle forces therefore both produce short-range SPP aggregation.

## Depends on

- [Quasi-static obstacle density under strong tethers](quasi-static-obstacle-density-under-strong-tethers.md)

## Expansion

To first order the obstacle density is $\rho_f = 1 + \tfrac{\gamma}{\eta}\partial_x^2(\phi * \rho_g)$. The SPP flux contains $\zeta^{-1}\rho_g\,\partial_x(\phi * \rho_f)$, and $\phi * \rho_f = \text{const} + \tfrac{\gamma}{\eta}(\phi * \phi'') * \rho_g$. Integrating by parts gives $\phi * \phi'' = \phi' * \phi' = W$. Differentiating $W$ in the distributional sense uses $\phi'' = \varphi'(|x|) + 2\varphi(0)\delta_0$. That gives $W'(x) = 2\varphi(0)\varphi(|x|)\operatorname{sign}(x) + \int \varphi'(|z|)\varphi(|x - z|)\operatorname{sign}(x - z)\,dz$. The second term vanishes at $0$ by symmetry, so the limit is $2\varphi(0)^2$. For $x \in (r_I, 2r_I)$ only the second term survives, and its integrand is a product of opposite-sign factors. Short-range attraction combined with self-repulsion and intermediate repulsion explains the size-controlled travelling clusters seen in simulations. A non-compact example, $\varphi_2(r) \propto e^{-r/r_I}$, gives $W_2'(x) \propto e^{-|x|/r_I}(2r_I - |x|)\operatorname{sign}(x)$: attractive for $|x| < 2r_I$ and repulsive beyond.

## Sources

- Aceves-Sanchez P, Degond P, Keaveny EE, Manhart A, Merino-Aceituno S, Peurichard D. Large-scale dynamics of self-propelled particles moving through obstacles: model derivation and pattern formation. *Bulletin of Mathematical Biology* 82 (2020) 129. <https://doi.org/10.1007/s11538-020-00805-z>. PMCID: PMC7519010.
