# Herd-immunity steady states and final-size-optimal social distancing in the controlled SIR model

**Model.** In time units of the infectious period ($\tau = \gamma t$) the SIR model with a time-varying reproduction number $\mathcal{R}(\tau) = \beta(\tau)/\gamma$ is

$$\dot S = -\mathcal{R}(\tau)SI, \qquad \dot I = \mathcal{R}(\tau)SI - I,$$

on $\mathcal{X} = \{S, I \ge 0,\ S + I \le 1\}$. Social distancing is a control $\mathcal{R}(\cdot) \in \Omega_{\mathcal{R}}$: $\mathcal{R}(\tau) \in [\underline{\mathcal{R}}, \bar{\mathcal{R}}]$ on a finite intervention window $[\tau_s, \tau_f]$ and $\mathcal{R}(\tau) = \bar{\mathcal{R}}$ outside it. Let $S^* = \min\{1, 1/\bar{\mathcal{R}}\}$ be the herd-immunity threshold without intervention.

**Theorem (equilibrium set and final size).** With $\mathcal{R} \equiv \bar{\mathcal{R}}$:
1. The set $\{(\bar S, 0) : 0 \le \bar S \le S^*\}$ is the unique asymptotically stable set, with domain of attraction $\mathcal{X}\setminus\{(\bar S,0):\bar S>S^*\}$; points with $\bar S > S^*$ are unstable equilibria, and no single equilibrium in the stable set is attractive (each is stable but not asymptotically stable).
2. Let $\Phi(S,I) = -W\big(-\bar{\mathcal{R}}S\,e^{-\bar{\mathcal{R}}(S + I)}\big)/\bar{\mathcal{R}}$ ($W$ the principal Lambert branch). From $(S(\tau_0), I(\tau_0))$ with $I(\tau_0) > 0$ the limit is $S_\infty = \Phi(S(\tau_0), I(\tau_0))$, and the epidemic final size is $1 - S_\infty$. (If $I(\tau_0) = 0$ the state is an equilibrium and $S_\infty = S(\tau_0)$.)
3. $\max_{\mathcal{X}}\Phi = S^*$, attained at $(S^*, 0)$, so $S_\infty < S^*$ from every state with $I(\tau_0) > 0$ and $\sup\{S_\infty : I(\tau_0) > 0\} = S^*$. For $\delta \in (0,1)$, the maximum of $\Phi$ over $\{(S,I) \in \mathcal{X} : I \ge \delta\}$ is attained at $(S^*, \delta)$ if $S^* + \delta \le 1$, with value $-W(-\bar{\mathcal{R}}S^*e^{-\bar{\mathcal{R}}(S^* + \delta)})/\bar{\mathcal{R}}$, and at $(1 - \delta, \delta)$ otherwise.
4. Starting from $(1 - \epsilon, \epsilon)$ with $S(0) > S^*$, every admissible control yields $S_\infty \le S^*$: the smallest achievable final size after interventions end is $1 - S^*$, reached only by arriving at herd immunity with vanishing prevalence.

**Theorem (control strategies).** Given a hospital capacity $I_{\max}$, the objective is $S(\tau) \to S^*$ with $I(\tau) \le I_{\max}$ for all $\tau$, at minimal cost $\int(\bar{\mathcal{R}} - \mathcal{R}(\tau))\,d\tau$. If a single-interval ("goldilocks") distancing with constant $\mathcal{R}$ achieving this exists, it is the only one approaching the objective as $\tau_f \to \infty$. The "wait, maintain, suspend" policy

$$\mathcal{R}(\tau) = \bar{\mathcal{R}} \text{ on } [0, \tau_s)\cup(\tau_f, \infty), \qquad \mathcal{R}(\tau) = 1/S(\tau) \text{ on } [\tau_s, \tau_1), \qquad \mathcal{R}(\tau) = \mathcal{R}^*_{si} \text{ on } [\tau_1, \tau_f],$$

which lets the outbreak grow until $I = I_{\max}$, holds prevalence constant ($\dot I = 0$), then applies a final constant level, approaches the objective arbitrarily well for suitable $0 \le \tau_s < \tau_1 < \tau_f$, and an optimal control exists.

## Proof sketch

$I$ decreases exactly when $\mathcal{R}S < 1$, so once $S$ is below $1/\bar{\mathcal{R}}$ the epidemic dies out after controls are lifted, while any state with $S > S^*$ and positive $I$ rebounds. Along trajectories $\log S - \bar{\mathcal{R}}(S + I)$ is conserved, which gives the Lambert-$W$ final size (for $I > 0$ the limit lies below $1/\bar{\mathcal R}$, which selects the principal branch, and $\Phi(\cdot,I)$ increases in $S$ up to $S^*$ and decreases after it) and shows that overshoot below $S^*$ is inevitable unless $I$ is small when $S$ crosses $S^*$. Holding $\mathcal{R} = 1/S$ freezes prevalence at $I_{\max}$ while $S$ declines linearly, so the epidemic can be steered to $(S^*, \approx 0)$, minimising both peak prevalence and final size without a second wave.

## Sources

- Juan Sereno, Alejandro Anderson, Antonio Ferramosca, Esteban A. Hernandez-Vargas and Alejandro Hernán González, "Minimizing the epidemic final size while containing the infected peak prevalence in SIR systems", *Automatica* 144 (2022), 110496, <https://doi.org/10.1016/j.automatica.2022.110496>. Preprint version: arXiv:2111.05652 (2021), Section 2 (stability theorem, final-size formula and maximum lemma), Section 3 (steady-state upper bound and control objectives) and Section 4 (goldilocks, wait–maintain–suspend and optimal-control theorems), <https://doi.org/10.48550/arXiv.2111.05652>.
