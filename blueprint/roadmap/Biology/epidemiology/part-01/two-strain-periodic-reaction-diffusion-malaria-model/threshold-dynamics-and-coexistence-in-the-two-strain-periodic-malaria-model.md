# Threshold dynamics and coexistence in the two-strain periodic malaria model

On a bounded domain $\Omega \subset \mathbb{R}^n$ with smooth boundary and Neumann conditions, let $I_1, I_2$ be humans infected with the sensitive and the resistant strain and $I_{v1}, I_{v2}$ the correspondingly infected mosquitoes. Total human density is at its stable steady state $N(x)$ and total mosquito density at its globally stable $\omega$-periodic state $M^*(t,x)$. With vector-bias parameters $p \ge l > 0$ (probabilities that a mosquito picks an infectious, resp. susceptible, human), biting rate $\beta(t,x)$ ($\omega$-periodic), and $Q = p(I_1+I_2) + l(N - I_1 - I_2)$,

$$

\begin{aligned}
\partial_t I_1 &= D_h\Delta I_1 - (d+\gamma_1)I_1 + \frac{c_1\beta\,l\,(N - I_1 - I_2)}{Q}\,I_{v1},\\
\partial_t I_{v1} &= D_v\Delta I_{v1} - \eta I_{v1} + \frac{\alpha_1\beta\,p\,I_1}{Q}\,(M^* - I_{v1} - I_{v2}),\\
\partial_t I_2 &= D_h\Delta I_2 - (d+\gamma_2)I_2 + \frac{c_2\beta\,l\,(N - I_1 - I_2)}{Q}\,I_{v2},\\
\partial_t I_{v2} &= D_v\Delta I_{v2} - \eta I_{v2} + \frac{\alpha_2\beta\,p\,I_2}{Q}\,(M^* - I_{v1} - I_{v2}),
\end{aligned}

$$

where the mosquito death rate $\eta(t,x)$ is $\omega$-periodic. The system generates an $\omega$-periodic semiflow with a global attractor. The full system is competitive between strains, while each single-strain subsystem is cooperative.

Let $\mathcal R_i = r(\mathcal L_i)$ be the basic reproduction number of strain $i$ (spectral radius of the periodic next-generation operator of the single-strain linearization at the disease-free state); $\mathcal R_i - 1$ has the sign of $r(P_i) - 1$ for the associated Poincaré map. Let $\hat{\mathcal R}_i$ be the invasion reproduction number of strain $i$, defined in the same way at the $\omega$-periodic endemic state of the other strain.

**Theorem.**

1. (Single strain.) If $\mathcal R_i \le 1$, the disease-free state of the strain-$i$ subsystem is globally asymptotically stable; if $\mathcal R_i > 1$, there is a unique positive $\omega$-periodic solution $(I_i^*, I_{vi}^*)$, globally asymptotically stable for nonzero initial data.
2. (Extinction.) If $\mathcal R_1 < 1$ and $\mathcal R_2 < 1$, the disease-free state is globally attractive.
3. (Competitive exclusion.) If $\mathcal R_1 > 1 > \mathcal R_2$ and strain 1 is initially present, solutions converge uniformly in $x$ to the sensitive-strain periodic state $E_1(t,x)$; symmetrically if $\mathcal R_2 > 1 > \mathcal R_1$.
4. (Coexistence.) If $\mathcal R_1, \mathcal R_2 > 1$ and $\hat{\mathcal R}_1, \hat{\mathcal R}_2 > 1$, the system has at least one positive $\omega$-periodic solution and is uniformly persistent: there is $\delta^* > 0$ with $\liminf_{t\to\infty}\min_{x}I_i, I_{vi} \ge \delta^*$, $i = 1,2$.

## Expansion

The single-strain subsystem is cooperative and subhomogeneous on the order interval bounded by $(N, M^*)$, so the theory of monotone periodic semiflows gives the threshold dichotomy in item 1. Item 2 follows by comparison with the linearized single-strain systems. For item 3, the absent strain decays because its linearization at the disease-free state has $r(P_j) < 1$, and the system becomes asymptotically autonomous with limit the strain-$i$ subsystem. Item 4 uses persistence theory for periodic semiflows: $\hat{\mathcal R}_i > 1$ makes each boundary periodic solution $E_j$ unstable to invasion by strain $i$, so the boundary is a uniform weak repeller.

## Sources

- Huijie Chu, Zhenguo Bai, "A two-strain reaction-diffusion malaria model with seasonality and vector-bias", arXiv (2022). Section 2 (model and well-posedness), Section 3 (definitions of $\mathcal R_i$, $\hat{\mathcal R}_i$, Theorem 3.1), Section 4 (Theorems 4.1–4.3). <https://doi.org/10.48550/arXiv.2201.05559>. Published version: Zeitschrift für angewandte Mathematik und Physik 74(1) (2023), article 21, <https://doi.org/10.1007/s00033-022-01905-7>; locators above refer to the arXiv version.
