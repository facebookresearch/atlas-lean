# Control reproduction number of the SEAIR model with vaccination and reinfection

**Model.** With $N = S + V + E + A + I + R$ and force of infection $\lambda = \beta(A + \eta I)/N$ (symptomatic cases less infectious by the factor $\eta$),

$$\dot S = r_1\Lambda + c_2V - (k_1 + \lambda)S, \qquad \dot V = r_2\Lambda + c_1S - (k_2 + \phi_1\lambda)V,$$

$$\dot E = \lambda\,(S + \phi_1V + \phi_2R) - k_3E, \qquad \dot A = p\gamma E - k_4A, \qquad \dot I = q\gamma E + a_2\sigma A - k_5I, \qquad \dot R = a_1\sigma A + \theta I - (\mu + \phi_2\lambda)R,$$

where a fraction $r_2 = 1 - r_1$ of recruits $\Lambda$ is vaccinated, susceptibles are vaccinated at rate $c_1$ and vaccine protection wanes at rate $c_2$, $\phi_1 = 1 - \epsilon$ for vaccine efficacy $\epsilon$, $\phi_2$ is the relative susceptibility of recovered individuals (reinfection), latents become asymptomatic or symptomatic with probabilities $p, q = 1-p$ at rate $\gamma$, asymptomatic cases recover or develop symptoms with probabilities $a_1, a_2 = 1-a_1$ at rate $\sigma$, symptomatic cases recover at rate $\theta$ and die of disease at rate $\delta$, and $k_1 = c_1 + \mu$, $k_2 = c_2 + \mu$, $k_3 = \mu + \gamma$, $k_4 = \mu + \sigma$, $k_5 = \mu + \delta + \theta$. The set $\{0 < N\le\Lambda/\mu\}$ of nonnegative states is invariant.

**Disease-free state and threshold.** The disease-free equilibrium has

$$S_0 = \frac{(c_2r_2 + r_1k_2)\Lambda}{k_1k_2 - c_1c_2}, \qquad V_0 = \frac{(k_1r_2 + c_1r_1)\Lambda}{k_1k_2 - c_1c_2}, \qquad S_0 + V_0 = N_0 = \frac\Lambda\mu,$$

and, with $N_1 = S_0 + \phi_1V_0$, the control reproduction number (spectral radius of the next-generation matrix) is

$$\mathcal R_c = \frac{N_1}{N_0}\,\frac{\beta\gamma}{k_3}\Big(\frac{p}{k_4} + \frac{\eta\,(a_2p\sigma + k_4q)}{k_4k_5}\Big).$$

**Theorem.**

1. The disease-free equilibrium is locally asymptotically stable if $\mathcal R_c < 1$ and unstable if $\mathcal R_c > 1$; it is globally asymptotically stable when $\mathcal R_c < 1$ provided $\frac{N_1}{N_0} \ge \frac{S + \phi_1V + \phi_2R}{N}$ along solutions.
2. Endemic equilibria are the positive roots of an explicit cubic $\mathcal A_3\lambda^{*3} + \mathcal A_2\lambda^{*2} + \mathcal A_1\lambda^* + \mathcal A_0 = 0$ in the equilibrium force of infection $\lambda^*$, with $\mathcal A_3 < 0$ and $\mathcal A_0 > 0$ when $\mathcal R_c > 1$. Hence, when $\mathcal R_c > 1$, the number of positive roots counted with multiplicity is odd: there is one endemic equilibrium, or up to three when $\mathcal A_2 > 0 > \mathcal A_1$. For $\mathcal R_c < 1$ the disease-free state can coexist with two endemic equilibria, suggesting a backward bifurcation.
3. (Reaction–diffusion extension.) For the same reaction terms with diffusion in each compartment and homogeneous Neumann boundary conditions on a bounded domain, solutions with nonnegative initial data are nonnegative, unique and bounded; the spatially homogeneous disease-free state is locally asymptotically stable iff $\mathcal R_c < 1$, and globally stable under the analogous pointwise condition.

## Depends on

- [Next-generation matrix and the basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/README.md)
- [SEIR epidemic model](../../seir-epidemic-model/README.md)

## Expansion

At the disease-free state only $E$ receives new infections, at rate $\beta(A + \eta I)N_1/N_0$, so the new-infection matrix has a single nonzero row and the transition matrix is lower triangular; $\mathcal R_c$ is the expected infectiousness of one latent, $p/k_4$ from the asymptomatic path plus $\eta/k_5$ times the probability $(q + pa_2\sigma/k_4)$ of becoming symptomatic, discounted by survival of latency $\gamma/k_3$ and by the effective susceptible fraction $N_1/N_0$. Neumann boundary conditions make the principal eigenfunction of the Laplacian constant, so linear stability of the homogeneous disease-free state in the PDE reduces to the ODE threshold, with diffusion only adding damping to nonconstant modes. Reinfection of recovered individuals and leaky vaccination feed new infections from compartments that are empty at the disease-free state, which is what allows a backward bifurcation.

## Sources

- Hamadjam Abboubakar, Reinhard Racke, Nicolas Schlosser, "ODE and PDE models for COVID-19, with reinfection and vaccination process for Cameroon and Germany", arXiv (2025). Section 2 (model, disease-free equilibrium, $\mathcal R_c$, local stability lemma, Theorem 1, Proposition 1), Section 4 (reaction–diffusion model, Theorems 2–4, Proposition 2). <https://doi.org/10.48550/arXiv.2504.21613>. Published version: Discrete and Continuous Dynamical Systems - B 36(0) (2026), 302–334, <https://doi.org/10.3934/dcdsb.2026034>; locators above refer to the arXiv version.
