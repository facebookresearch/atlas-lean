# Hyperbolic leader–follower swarm model with nonlocal turning

Let $u^\pm(x, t)$ and $v^\pm(x, t)$ be the densities of followers and leaders moving right ($+$) or left ($-$) on a line (in simulations, a ring $[0, L]$ with periodic boundary conditions). Followers move at speed $\gamma$, leaders at speeds $\beta_\pm$, and individuals reverse direction at rates $\lambda^{u^\pm}, \lambda^{v^\pm}$ (Eq. 1):

$$\partial_t u^\pm \pm \gamma\, \partial_x u^\pm = \mp \lambda^{u^+} u^+ \pm \lambda^{u^-} u^-, \qquad \partial_t v^\pm \pm \beta_\pm\, \partial_x v^\pm = \mp \lambda^{v^+} v^+ \pm \lambda^{v^-} v^-.$$

**Turning rates** (Eqs. 2–4). For $i \in \{u, v\}$,

$$\lambda^{i^\pm} = \lambda_1 + \lambda_2\, f(y^{i^\pm}), \qquad f(y) = \tfrac12 + \tfrac12 \tanh(y - y_0), \qquad y^{i^\pm} = Q_r^{i^\pm} + Q_a^{i^\pm} + Q_l^{i^\pm},$$

so the rate rises from the baseline $\lambda_1$ toward $\lambda_1 + \lambda_2$ with the perceived signal $y$.

**Nonlocal signals** (Eqs. 5–6). With total densities $u = u^+ + u^-$, $v = v^+ + v^-$ and kernels $K_r, K_a, K_l$ on $(0, \infty)$,

$$Q_r^{i^\pm} = q_r \int_0^\infty K_r(s)\big[(u + v)(x \pm s) - (u + v)(x \mp s)\big]\, ds, \qquad Q_a^{i^\pm} = -q_a \int_0^\infty K_a(s)\big[(u + v)(x \pm s) - (u + v)(x \mp s)\big]\, ds,$$

Repulsion and attraction act identically on both groups. The groups differ in alignment (Eqs. 9–10): leaders ignore the swarm and receive a constant bias toward the target in the $+$ direction, while followers react to oncoming individuals,

$$Q_l^{v^\pm} = \mp 2q_l\,\varepsilon\int_0^\infty K_l(s)\,ds,$$

$$Q_l^{u^\pm} = q_l\int_0^\infty K_l(s)\big[u^\mp(x \pm s) + \alpha^\mp v^\mp(x \pm s) - u^\pm(x \mp s) - \alpha^\pm v^\pm(x \mp s)\big]\, ds .$$

The three leader biases of Table 1 act in different terms: the **orientation bias** $\varepsilon \ge 0$ enters leader turning through $Q_l^{v^\pm}$ (for $\varepsilon > 0$ it lowers the turning signal of $v^+$ and raises that of $v^-$); the **speed bias** $\beta_+ \ne \beta_-$ enters leader transport in Eq. 1; and the **conspicuousness bias** $\alpha^+ \ne \alpha^-$ (weights $\alpha^\pm \ge 0$, with $\alpha^\pm = 1$ for leaders indistinguishable from followers) enters follower turning through $Q_l^{u^\pm}$.

**Conservation.** On the periodic domain the turning terms cancel pairwise, so the follower mass $\int (u^+ + u^-)\, dx$ and the leader mass $\int (v^+ + v^-)\, dx$ are separately conserved.

## Expansion

Adding the two follower equations gives $\partial_t u + \gamma\, \partial_x (u^+ - u^-) = 0$, a conservation law, and likewise for leaders. Expanding the nonlocal integrals in $s$ shows that $Q_r$ and $Q_a$ act like gradients of total density: moving toward higher density increases turning under repulsion and decreases it under attraction, producing cohesive swarms. The model asks which leader biases let a minority of informed individuals steer the whole group toward a target.

## Sources

- S. Bernardi, R. Eftimie, K. J. Painter, *Leadership through influence: what mechanisms allow leaders to steer a swarm?*, Bull. Math. Biol. (2021). <https://doi.org/10.1007/s11538-021-00901-8> (PMCID: PMC8110512)
