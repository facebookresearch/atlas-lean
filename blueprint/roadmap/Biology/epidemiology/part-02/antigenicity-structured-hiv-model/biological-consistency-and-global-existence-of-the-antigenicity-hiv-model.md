# Biological consistency and global existence of the antigenicity HIV model

**Model.** The antigenicity model of HIV dynamics tracks, for each antigenicity class $j$, healthy CD4 lymphocytes $T_j$ adapted to that class, infected lymphocytes $U_j$, infectious virions $V_j$ and non-infectious virions $W_j$. Lymphocytes are produced constitutively, are recruited in proportion to the virus load of their own antigenicity, kill only viruses of matching antigenicity, and are infected through a saturating function $J$ of the virus-to-lymphocyte ratio. With a single antigenicity class (so mutation disappears) and after scaling cell numbers by the uninfected equilibrium $\gamma/\beta$, the system reads

$$\frac{dT}{dt} = \beta(1 - T) - \frac{T}{\tau} J\Big(\frac{V}{T}\Big) + \omega (V + W) T, \qquad \frac{dU}{dt} = \frac{T}{\tau} J\Big(\frac{V}{T}\Big) - \alpha U,$$

$$\frac{dV}{dt} = a\theta U - \zeta V T, \qquad \frac{dW}{dt} = a(1-\theta) U - \zeta W T,$$

where time is in days, $\theta \in (0,1)$ is the infectious fraction of the burst $a$, $\omega$ is the antigen-driven lymphocyte production rate and $\zeta$ the lymphocyte killing rate of virions.

**Hypotheses.** $\beta, \tau, \omega, \alpha, \zeta > 0$ and $0 < \theta < 1$; $J$ is concave on $[0,\infty)$, $J(0) = 0$, $J'(0) = 1$, $J(x) \to 1$ as $x \to \infty$, and $J$ is bounded on $(-\infty, 0]$ (for example $J = \tanh$). The admissible set is $\mathcal{B} = \{(T,U,V,W) : T > 0,\ U, V, W \ge 0\}$.

**Theorem (biological consistency).** The solution with initial condition in $\mathcal{B}$ remains in $\mathcal{B}$; in particular $T(t) > 0$ for as long as the solution is defined.

**Theorem (global existence).** Let $\eta = a\omega - \alpha\zeta$ and $\gamma = |\eta/\zeta|$. For initial data $(T_0, U_0, V_0, W_0) \in \mathcal{B}$, the weighted total $\Phi(t) = T + U + \frac{\omega}{\zeta}(V + W)$ satisfies

$$\Phi(t) \le \Phi(0) + \beta t \quad \text{if } \eta \le 0, \qquad \Phi(t) \le \Phi(0)\, e^{\gamma t} + \frac{\beta}{\gamma}\big(e^{\gamma t} - 1\big) \quad \text{if } \eta > 0.$$

Hence the solution stays finite and exists for all $t \in [0, \infty)$.

## Expansion

Positivity is proved by contradiction at the first time a component reaches the boundary of $\mathcal{B}$, distinguishing according to how many of $U, V, W$ vanish initially; $T$ cannot reach $0$ because $\beta(1-T) > 0$ near $T = 0$ while $T J(V/T)/\tau$ stays bounded. For the bound, adding the equations gives

$$\frac{d\Phi}{dt} = \beta(1 - T) - \alpha U + \frac{a\omega}{\zeta} U \le \beta + \frac{\eta}{\zeta} U,$$

because the infection and killing terms cancel in this weighted sum. When $\eta \le 0$ the last term is non-positive; when $\eta > 0$ it is at most $\gamma \Phi$, and Gronwall's inequality gives the exponential bound. The infection term $T J(V/T)/\tau$ replaces mass action; it behaves like $V/\tau$ when virus is scarce and saturates at $T/\tau$ when virus is abundant.

## Sources

- F. Dubois, H. V. J. Le Meur and C. Reiss, "Mathematical modeling of antigenicity for HIV dynamics", MathS In Action 3 (2010), no. 1, 1–35; arXiv:0810.2988: model in Section 3 (system of Section 3-4), dimensionless system and Theorem 7 (biological consistency, Section 4-1), Theorem 13 (global existence, Section 4-2). <https://doi.org/10.48550/arXiv.0810.2988>. Published version: MathematicS In Action 3(1) (2010), 1–35, <https://doi.org/10.5802/msia.3>; locators above refer to the arXiv version.
