# Basic offspring number and feedback elimination by sterile male releases

**Model.** For *Aedes* mosquitoes, let $E$ be the aquatic phase, $M$ fertile males and $F$ females inseminated by fertile males. The uncontrolled system is

$$
\dot E = \beta_E F\Bigl(1 - \frac{E}{K}\Bigr) - (\nu_E + \delta_E)E, \qquad
\dot M = (1-\nu)\nu_E E - \delta_M M, \qquad
\dot F = \nu\nu_E E - \delta_F F,
$$

with positive parameters (egg-laying rate $\beta_E$, carrying capacity $K$, emergence rate $\nu_E$, female fraction $\nu \in (0,1)$, mortalities $\delta_E, \delta_M, \delta_F$). Releasing sterile males at rate $u(t) \ge 0$ adds $\dot M_s = u - \delta_s M_s$ and replaces the female recruitment by $\nu\nu_E E\,M/(M + \gamma M_s)$, where $\gamma > 0$ is the relative mating competitiveness of sterile males.

**Results.**
1. *(Basic offspring number.)* Let $\mathcal{N} = \dfrac{\beta_E \nu \nu_E}{(\nu_E + \delta_E)\delta_F}$. If $\mathcal{N} \le 1$, the extinction equilibrium $\mathbf{E}_0 = 0$ is the only equilibrium and is globally asymptotically stable on $\mathbb{R}^3_+$. If $\mathcal{N} > 1$, there is also

$$
\mathbf{E}^* = K\Bigl(1 - \frac{1}{\mathcal{N}}\Bigr)\Bigl(1, \frac{(1-\nu)\nu_E}{\delta_M}, \frac{\nu\nu_E}{\delta_F}\Bigr),
$$

globally asymptotically stable on $\mathbb{R}^3_+ \setminus \{(0, M, 0)\}$. For $\mathcal{N} \ne 1$ these equilibria are exponentially stable.
2. *(Apparent reproduction number.)* Along controlled trajectories define $\mathcal{N}_{\mathrm{app}}(t) = \mathcal{N}\,M(t)/(M(t) + \gamma M_s(t))$. If the releases ensure $\mathcal{N}_{\mathrm{app}}(t) \le \theta$ for all $t \ge T$, for some $\theta \in (0,1)$, then $(E, M, F)$ converges exponentially to $\mathbf{E}_0$, uniformly over initial conditions below a fixed upper bound.
3. *(State feedback.)* If, for constants $\alpha > (\mathcal{N} - 1)/\gamma$ and $\omega > 0$,

$$
u(t) \ge \alpha\,|\dot M(t)|_+ + \omega\alpha M(t) + (\delta_s - \omega) M_s(t), \qquad t \ge 0,
$$

then every trajectory converges exponentially to $\mathbf{E}_0$. Robust versions hold when only upper and lower bounds on the parameters and on the states (from interval observers driven by measured male counts) are known.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof sketch

$\mathcal{N}$ is the expected number of fertilized females produced by one fertilized female in an empty habitat: she lays at rate $\beta_E$ for a mean time $1/\delta_F$, and each egg survives the aquatic phase and becomes a female with probability $\nu\nu_E/(\nu_E + \delta_E)$. The system is monotone, so bounds propagate along trajectories. Sterile males act only by diluting the fertile mating pool, which multiplies $\mathcal{N}$ by $M/(M + \gamma M_s)$; keeping this apparent number below $1$ makes the population behave like a subcritical one. The feedback law achieves this by keeping $\gamma M_s \ge \alpha\gamma M$ with $\alpha\gamma > \mathcal{N} - 1$, which forces $\mathcal{N}_{\mathrm{app}} < 1$; the $|\dot M|_+$ term anticipates increases in the wild male population.

## Sources

- P.-A. Bliman, "Basic offspring number and robust feedback design for the biological control of vectors by sterile insect release technique", in *Proceedings of the 2025 European Control Conference (ECC)*, Thessaloniki, Greece, June 2025. Preprint version: arXiv:2410.23729 (2024), uncontrolled and controlled models, Theorems 1–4, 6, <https://doi.org/10.48550/arXiv.2410.23729>.
