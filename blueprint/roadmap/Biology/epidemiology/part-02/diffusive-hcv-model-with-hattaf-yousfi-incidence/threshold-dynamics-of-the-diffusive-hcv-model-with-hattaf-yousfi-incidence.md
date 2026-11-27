# Threshold dynamics of the diffusive hepatitis C model with Hattaf–Yousfi incidence

**Model.** On a bounded smooth domain $\Omega \subset \mathbb R^n$ with homogeneous Neumann boundary conditions, healthy hepatocytes $H$, infected hepatocytes $I$ and free virions $V$ satisfy

$$\begin{aligned} \partial_t H &= D_1 \Delta H + \lambda - dH - f(H,V) + \rho I, \\ \partial_t I &= D_2 \Delta I + f(H,V) - (\alpha + \rho) I, \\ \partial_t V &= D_3 \Delta V + (1-\varepsilon) k I - \mu V - u f(H,V), \end{aligned}$$

with the Hattaf–Yousfi functional response

$$f(H,V) = \frac{(1-\eta)\beta H V}{\alpha_0 + \alpha_1 H + \alpha_2 V + \alpha_3 H V},$$

which contains mass action, saturation, Beddington–DeAngelis and Crowley–Martin incidences as special cases. Here $\lambda, d, \beta, \alpha, k, \mu, \alpha_0 > 0$; $\alpha_1, \alpha_2, \alpha_3, \rho \ge 0$; $\rho$ is the cure rate of infected cells, $u \in \{0,1\}$ switches the loss of virions on entry, and $\eta, \varepsilon \in [0,1)$ are the efficacies of drugs blocking infection and virion production. Write $\Lambda = \lambda/d$ and

$$\mathcal R_0 = \frac{(1-\eta)(1-\varepsilon) k \beta \Lambda}{(\alpha+\rho)\big[\mu(\alpha_0 + \alpha_1\Lambda) + u(1-\eta)\beta\Lambda\big]}, \qquad \tau_0 = \frac{(1-\eta)(1-\varepsilon) k \beta \Lambda}{\mu\,\alpha_0\,(\alpha+\rho)} \ \ge \mathcal R_0 .$$

**Theorem.** For nonnegative Hölder-continuous initial data compatible with the boundary condition, the problem has a unique global nonnegative bounded solution. Moreover:

1. If $\mathcal R_0 \le 1$ the only spatially homogeneous equilibrium is the uninfected state $E_0 = (\Lambda, 0, 0)$; if $\mathcal R_0 > 1$ there is in addition a unique spatially homogeneous infected equilibrium $E^* = (H^*, I^*, V^*)$ with $0 < H^* < \Lambda$ and $I^*, V^* > 0$.
2. $E_0$ is locally asymptotically stable if $\mathcal R_0 \le 1$ and unstable if $\mathcal R_0 > 1$; it is globally asymptotically stable in the positively invariant region whenever $\tau_0 < 1$.
3. If $\mathcal R_0 > 1$, then $E^*$ is globally asymptotically stable.

Diffusion therefore does not change the threshold: the long-run outcome is decided by the same $\mathcal R_0$ as the ODE model, which drug therapy lowers through the factors $(1-\eta)(1-\varepsilon)$.

## Expansion

Existence uses the sectorial Laplacian with Neumann conditions, an analytic semigroup, and a variational formulation for the nonlinear coupling; positivity and an $L^\infty$ bound follow from comparison and the total-cell balance. $\mathcal R_0$ is the spectral radius of the next-generation matrix at $E_0$ for the infected compartments $(I, V)$, where the loss term $u f$ adds $u(1-\eta)\beta\Lambda/(\alpha_0+\alpha_1\Lambda)$ to the virion removal rate. Global stability comes from Lyapunov functionals of the form $\int_\Omega \big(\Phi(H/H^*) H^* + \Phi(I/I^*) I^* + c\,\Phi(V/V^*) V^*\big)\,dx$ with $\Phi(z) = z - 1 - \ln z$, whose diffusion terms are nonpositive after integration by parts under the Neumann condition, combined with LaSalle's invariance principle; at $E_0$ the bound $f(H,V) \le (1-\eta)\beta H V/\alpha_0$ gives the sufficient condition $\tau_0 < 1$.

## Sources

- Alexis Nangue, Bruno Nde Tchiffo, "Global analysis of a spatiotemporal cellular model for the transmission of hepatitis C virus with Hattaf-Yousfi functional response", arXiv (2021). Section 2 (model), Theorem 3 (well-posedness), Section 4 ($\mathcal R_0$, $\tau_0$), Theorems 4–8. <https://doi.org/10.48550/arXiv.2111.03312>. Published version: European Journal of Mathematical Analysis 3 (2021), article 1, <https://doi.org/10.28924/ada/ma.3.1>; locators above refer to the arXiv version.
