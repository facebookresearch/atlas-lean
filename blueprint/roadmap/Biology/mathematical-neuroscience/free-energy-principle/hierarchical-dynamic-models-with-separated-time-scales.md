# Hierarchical dynamic models with separated time-scales

**Model.** A two-level hierarchical dynamic model generates data $y$ from hidden states $x^{(1)}, x^{(2)}$ and a causal state $v^{(1)}$ by

$$\begin{aligned}
y &= g\big(x^{(1)}\big) + z^{(1)}, & \dot x^{(1)} &= f\big(x^{(1)}, v^{(1)}\big)/T^{(1)} + w^{(1)},\\
v^{(1)} &= g\big(x^{(2)}\big) + z^{(2)}, & \dot x^{(2)} &= f\big(x^{(2)}, v^{(2)}\big)/T^{(2)} + w^{(2)},
\end{aligned}$$

with Gaussian fluctuations $z^{(i)}, w^{(i)}$ of fixed precisions, time constants $T^{(2)} \gg T^{(1)}$, and the output of the slow level acting as a control parameter of the fast level. In the birdsong example both levels are Lorenz systems,

$$f(x, v) = \begin{pmatrix} a(x_2 - x_1) \\ v x_1 - x_2 - x_1 x_3 \\ x_1 x_2 - c x_3 \end{pmatrix}, \qquad a = 10,\ c = 8/3,$$

with $T^{(1)} = 0.25\,\mathrm{s}$, $T^{(2)} = 2\,\mathrm{s}$ and fixed Rayleigh number $v^{(2)} = 32$ at the slow level; the slow level's output is the Rayleigh number $v^{(1)}$ of the fast level, switching it between fixed-point, periodic and chaotic regimes.

**Generalized coordinates of motion.** States are represented together with their temporal derivatives, $\tilde u = (u, u', u'', \dots)$. Truncating at order $p$, the trajectory near time $t$ is encoded by the Taylor polynomial

$$u(t + \Delta t) \approx \sum_{k=0}^{p} \frac{u^{(k)}(t)}{k!}\, \Delta t^{k},$$

so a point in generalized coordinates specifies a local trajectory, and the precision assigned to each order sets how far into the past and future that trajectory is represented with confidence.

**Properties.**

1. The hierarchy induces empirical priors: the slow level constrains the fast level's control parameter, so inferring $x^{(2)}$ from fast data recovers a slowly varying "syntax" that is never directly observed.
2. Inversion by minimizing variational free energy over generalized-coordinate conditional means yields recognition dynamics in which expectations at each level track their own time-scale. Removing the second level (a synthetic lesion) leaves larger first-level prediction errors on the same data, and a smaller, shorter omission response when the input stops unexpectedly, because the single-level model cannot represent the slowly changing control parameter.

## Depends on

- [Variational free energy as an upper bound on surprise](variational-free-energy-bound-on-surprise.md)

## Expansion

Scaling the flow by $1/T^{(i)}$ makes the second level evolve about an order of magnitude more slowly than the first, so its output appears quasi-static to the fast level over many fast cycles; this separation of time-scales is what lets a slowly changing cause be inferred from fast sensory input. The generative model plus Gaussian assumptions define the likelihood $p(y \mid u, m)$ and structural priors; generalized coordinates add priors on the coupling of motion between orders (each order is the derivative of the one below), which enforce smooth trajectory estimates and enable online inversion. The account motivates a rostro-caudal hierarchy of environmental time-scales in cortex, with higher areas encoding slower causes that modulate faster dynamics through backward connections.

## Sources

- Kiebel SJ, Daunizeau J, Friston KJ, "A hierarchy of time-scales and the brain" (2008), Methods, "A Generative Birdsong Model" (Equations (1)–(2)) and "Generalised Coordinates of Motion" (Equation (6)), and Results, "A Synthetic Lesion Study", <https://doi.org/10.1371/journal.pcbi.1000209>, PMCID PMC2568860.
