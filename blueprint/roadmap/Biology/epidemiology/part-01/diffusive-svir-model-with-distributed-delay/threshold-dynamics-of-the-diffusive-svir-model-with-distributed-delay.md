# Threshold dynamics of the diffusive SVIR model with distributed delay

On a bounded smooth domain $\Omega \subset \mathbb R^n$ with homogeneous Neumann boundary conditions, let $S,V,I$ be the densities of susceptible, vaccinated (imperfectly protected) and infected individuals, governed by

$$\partial_t S - d_S\Delta S = \Lambda - S\int_0^k g(\tau) f(I(t-\tau,x))\,d\tau - (\mu+\alpha)S,$$

$$\partial_t V - d_V\Delta V = \alpha S - V\int_0^k g(\tau) h(I(t-\tau,x))\,d\tau - (\gamma_1+\mu)V,$$

$$\partial_t I - d_I\Delta I = S\int_0^k g(\tau) f(I(t-\tau,x))\,d\tau + V\int_0^k g(\tau) h(I(t-\tau,x))\,d\tau - (\gamma+\mu+c)I,$$

with recovered class $\partial_t R - d_R\Delta R = \gamma_1 V + \gamma I - \mu R$ decoupled. Here $\Lambda$ is recruitment, $\mu$ natural death, $\alpha$ vaccination rate, $1/\gamma_1$ the time to immunity after vaccination, $\gamma$ recovery, $c$ disease death, all diffusion rates positive, and the delay kernel $g \ge 0$ satisfies $\int_0^k g = 1$. The incidence functions $f,h$ are $C^1$ with $f(0) = h(0) = 0$ and satisfy

- $(H_1)$ $f(I) > 0$, $h(I) > 0$ for $I > 0$;
- $(H_2)$ $f' > 0$, $h' > 0$, $f'' \le 0$, $h'' \le 0$ on $[0,\infty)$.

The disease-free equilibrium is $E_0 = (S_0,V_0,0)$ with $S_0 = \Lambda/(\mu+\alpha)$, $V_0 = \alpha\Lambda/\big((\mu+\alpha)(\gamma_1+\mu)\big)$, and

$$\mathcal R_0 = \frac{S_0 f'(0) + V_0 h'(0)}{\gamma+\mu+c}.$$

**Theorem.**

1. For any nonnegative continuous initial history the system has a unique nonnegative global solution.
2. If $\mathcal R_0 > 1$ there is a unique endemic equilibrium $E^* = (S^*,V^*,I^*)$ with $S^* = \Lambda/(f(I^*)+\mu+\alpha)$ and $V^* = \alpha\Lambda/\big((h(I^*)+\gamma_1+\mu)(f(I^*)+\mu+\alpha)\big)$.
3. Under $(H_1)$–$(H_2)$, $E_0$ is globally asymptotically stable if $\mathcal R_0 < 1$.
4. If $\mathcal R_0 > 1$, $E^*$ is globally asymptotically stable.

Theorem 3 of the source prints "globally asymptotically stable if and only if $\mathcal R_0<1$"; its proof gives only the "if" direction, and its Lyapunov functional also has nonpositive derivative at $\mathcal R_0=1$, where LaSalle's principle gives global stability of $E_0$ as well, so the printed "only if" fails at $\mathcal R_0=1$. Item 3 therefore states the sufficient condition only.

Diffusion and the distribution of the latency delay do not affect the threshold.

## Expansion

Concavity in $(H_2)$ gives $f(I) \le f'(0)I$ and $h(I) \le h'(0)I$, so near $E_0$ the infection term is dominated by its linearization, whose spectral bound changes sign at $\mathcal R_0 = 1$. Global stability uses Volterra-type Lyapunov functionals $\int_\Omega \big(S^*\phi(S/S^*) + V^*\phi(V/V^*) + I^*\phi(I/I^*)\big)dx$ with $\phi(u) = u - 1 - \ln u$, plus delay integrals of $\phi$ applied to the incidence ratios; Neumann boundary conditions make the diffusion contributions nonpositive after integration by parts, and LaSalle's invariance principle concludes. Uniqueness of $E^*$ follows from the monotonicity and concavity of $f$ and $h$.

## Sources

- Achraf Zinihi, Mostafa Tahiri, Moulay Rchid Sidi Ammi, "Stability analysis of a diffusive SVIR epidemic model with distributed delay, imperfect vaccine and general incidence rate", arXiv (2024). Section 2 (model and hypotheses), Theorems 1–4 (Sections 3–5). <https://doi.org/10.48550/arXiv.2405.15478>. Published version: in Mathematical Analysis (Chapman and Hall/CRC, 2025), 344–366, <https://doi.org/10.1201/9781003530602-15>; locators above refer to the arXiv version.
