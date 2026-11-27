# Fluid limit and threshold vaccination for SIR on the configuration model

**Model.** Take a configuration-model random graph on $n$ nodes with i.i.d. degrees of law $p = (p_k)$ (converging, with finite second moment). A susceptible node is infected at rate $r$ along each edge to an infected neighbor; infected nodes recover at rate $\gamma$; a susceptible node of degree $k$ is vaccinated at rate $\pi_t(k) = \xi(k)\pi_t$ with a measurable control $\pi : [0,T] \to [0,\nu]$ (e.g. $\xi \equiv 1$ for uniform, $\xi(k) = k$ for acquaintance vaccination). Recovered and vaccinated are absorbing. Edge-based variables: with $N^S_t$ the number of half-edges at susceptible nodes and $N^{IS}_t, N^{RS}_t, N^{VS}_t$ the numbers of edges from susceptibles to infected, recovered and vaccinated nodes, set $p^I = N^{IS}/N^S$, $p^R = N^{RS}/N^S$, $p^V = N^{VS}/N^S$, $p^S = 1 - p^I - p^R - p^V$.

**Theorem (fluid limit).** If the rescaled degree measures of the four classes converge initially, they converge in distribution in Skorokhod space to the unique solution of a deterministic measure-valued system. In the limit, with

$$\alpha_t = e^{-\int_0^t r p^I_s\,ds}, \qquad \theta_t = e^{-\int_0^t \pi_s\,ds}, \qquad g(\alpha,\theta) = \sum_k \mu^S_0(k)\,\alpha^k\theta^{\xi(k)},$$

a susceptible node of degree $k$ has escaped infection with probability $\alpha_t^k$ and vaccination with probability $\theta_t^{\xi(k)}$, the susceptible fraction is $S_t = g(\alpha_t,\theta_t)$, and

$$\dot\alpha = -r p^I\alpha, \qquad \dot\theta = -\pi\theta, \qquad \dot I = -\gamma I + r p^I\alpha\,\partial_\alpha g(\alpha,\theta), \qquad \dot V = \pi\theta\,\partial_\theta g(\alpha,\theta),$$

closed by Lipschitz ODEs for $p^S, p^I, p^V$ whose coefficients involve $\alpha\,\partial_{\alpha\alpha}g/\partial_\alpha g$ and $\partial_{\alpha\theta}g/\partial_\alpha g$; this finite system has a unique solution for every admissible control. For $\xi(k) = ak + b$ everything is expressed through the degree generating function $\psi(z) = \sum_k \mu^S_0(k)z^k$: with $\beta_t = e^{-\int_0^t(rp^I_s + a\pi_s)ds}$ and $\phi_t = e^{-\int_0^t b\pi_s ds}$, $S_t = \phi_t\psi(\beta_t)$ and the dynamics depend on the degree law through $\beta\psi''(\beta)/\psi'(\beta)$.

**Theorem (optimal vaccination).** For the limiting equations with costs of infection and of vaccination:

1. in the decentralized (game) setting, the optimal strategy of a node of degree $k$ is of threshold type, $\tilde\pi^{*}_t = \nu\mathbf 1_{[0,\tau_k]}(t)$;
2. if $\xi$ is increasing, the thresholds are increasing in degree: $\tau_k > \tau_j$ for $k > j$;
3. in the centralized setting the cost-minimizing control is also of threshold type.

## Expansion

Conditionally on the degree, the infection and vaccination clocks of a susceptible node are independent Poisson clocks driven by the mean fields $rp^I_t$ (per edge) and $\xi(k)\pi_t$, which gives the product $\alpha_t^k\theta_t^{\xi(k)}$ and reduces the infinite system to the generating function $g$, as in edge-based (Volz–Miller) SIR theory. Martingale estimates for the empirical measures and tightness in Skorokhod space give the fluid limit. In the control problems the Hamiltonian is linear in $\pi$, so Pontryagin's principle gives bang–bang controls; the switching function has a single sign change, giving one threshold, and higher-degree nodes face more infectious contacts and keep vaccinating longer.

## Sources

- Emanuel Javier Ferreyra, Matthieu Jonckheere, Juan Pablo Pinasco, "SIR dynamics with vaccination in a large configuration model", arXiv (2019). Section 2 (model and edge-based variables), Section 3 (main convergence theorem, reduced system and the $\xi(k) = ak + b$ case), Section 4 (threshold optimal strategies). <https://doi.org/10.48550/arXiv.1912.12350>. Published version: Applied Mathematics & Optimization 84(S2) (2021), 1769–1818, <https://doi.org/10.1007/s00245-021-09810-7>; locators above refer to the arXiv version.
