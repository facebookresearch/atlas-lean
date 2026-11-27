# Global stability of the diffusive SEIR model with distributed delay

**Model.** On a bounded smooth domain $\Omega \subset \mathbb R^n$ with homogeneous Neumann boundary conditions,

$$\begin{aligned}
\partial_t S - k_S\Delta S &= b - \mu S - \beta\int_0^h g(\tau)\,f\big(S(x,t), I(x,t-\tau)\big)\,d\tau,\\
\partial_t E - k_E\Delta E &= \beta\int_0^h g(\tau)\,f\big(S(x,t), I(x,t-\tau)\big)\,d\tau - (\mu + \alpha)E,\\
\partial_t I - k_I\Delta I &= \alpha E - (\mu + c + \gamma)I,
\end{aligned}$$

and $\partial_t R - k_R\Delta R = \gamma I - \mu R$ (decoupled). Here $b$ is recruitment, $\mu$ natural death, $\alpha$ the rate of becoming infectious, $c$ disease death, $\gamma$ recovery, $k_\bullet > 0$ diffusion coefficients and $g \ge 0$ a delay kernel on $[0,h]$ with $\int_0^h g = 1$. The incidence $f$ satisfies $f(0,I) = f(S,0) = 0$ and
- $(H_1)$ $f$ is strictly increasing in $S$ for fixed $I > 0$ and increasing in $I$ for fixed $S$;
- $(H_2)$ $f(S,I)/I$ is bounded and decreasing in $I > 0$ for fixed $S$.

This covers bilinear, saturated and Beddington–DeAngelis-type incidences.

**Theorem.** The system is well posed in the space of continuous non-negative initial histories and its solutions are bounded. Let $S_0 = b/\mu$ and

$$R_0 = \frac{\beta\alpha\,\partial_I f(S_0, 0)}{(\mu+\alpha)(\mu+\gamma+c)}.$$

1. The disease-free equilibrium $(S_0, 0, 0)$ is globally asymptotically stable if and only if $R_0 \le 1$.
2. If $R_0 > 1$, there is a unique spatially homogeneous endemic equilibrium $(S^*, E^*, I^*)$, it is the only equilibrium besides the disease-free one, and it is globally asymptotically stable.

Diffusion and the distributed delay therefore do not change the threshold or the global outcome of the ODE SEIR model.

## Proof sketch

Well-posedness writes the system as an abstract retarded equation $u' = Au + F(u_t)$ with $A$ the Neumann Laplacian and uses the analytic semigroup $T(t)$ in the mild formulation $u(t) = T(t)\phi(0) + \int_0^t T(t-s)F(u_s)\,ds$; boundedness follows from the equation for $S + E + I$. For stability, integrate over $\Omega$ a Volterra-type Lyapunov functional. At the endemic state use a functional of the form

$$\int_\Omega\Big[S - S^* - \int_{S^*}^S\frac{f(S^*,I^*)}{f(\sigma,I^*)}d\sigma + E - E^* - E^*\ln\frac{E}{E^*} + \frac{\mu+\alpha}{\alpha}\Big(I - I^* - I^*\ln\frac{I}{I^*}\Big) + \text{delay terms}\Big]dx,$$

where the delay terms are $\beta f(S^*,I^*)\int_0^h g(\tau)\int_{t-\tau}^t \Phi\big(f(S^*,I(s))/f(S^*,I^*)\big)\,ds\,d\tau$ with $\Phi(u) = u - 1 - \ln u$. Diffusion contributes only non-positive terms such as $-k_S S^*\int_\Omega |\nabla S|^2/S^2$ via Green's formula and the Neumann condition, and $(H_1)$–$(H_2)$ make the remaining reaction terms non-positive. LaSalle's invariance principle finishes both cases.

## Sources

- Abdesslem Lamrani Alaoui, Moulay Rchid Sidi Ammi, Mouhcine Tilioua and Delfim F.M. Torres, "Global stability of a diffusive SEIR epidemic model with distributed delay", in *Mathematical Analysis of Infectious Diseases*, Elsevier, 2022, 191–209, <https://doi.org/10.1016/b978-0-32-390504-6.00016-4>. Preprint version: arXiv:2202.02143 (2022), model, hypotheses $(H_1)$–$(H_2)$, existence and boundedness propositions, basic reproduction number, endemic equilibrium theorem and the global stability theorems, <https://doi.org/10.48550/arXiv.2202.02143>.
