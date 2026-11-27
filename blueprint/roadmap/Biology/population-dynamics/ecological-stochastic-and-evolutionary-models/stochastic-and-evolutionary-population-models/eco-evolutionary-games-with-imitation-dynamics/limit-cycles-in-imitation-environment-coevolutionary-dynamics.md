# Limit cycles in imitation–environment coevolutionary dynamics

**Model.** Let $x \in [0,1]$ be the frequency of cooperators and $n \in [0,1]$ the environmental state. The payoff matrix interpolates between a depleted-environment game and a replete-environment game,

$$A(n) = (1-n)\begin{pmatrix} R_0 & S_0\\ T_0 & P_0\end{pmatrix} + n\begin{pmatrix} R_1 & S_1 \\ T_1 & P_1\end{pmatrix},\qquad R_0 > T_0,\ S_0 > P_0,\ R_1 < T_1,\ S_1 < P_1,$$

so cooperation dominates when $n=0$ and defection when $n=1$; $\pi_C(x,n), \pi_D(x,n)$ are the resulting expected payoffs. Strategies spread by pairwise imitation with an *imitation function* $g:\mathbb{R}\to(0,1]$, strictly increasing and $C^1$, and imitation intensity $\beta \ge 0$; cooperators improve and defectors degrade the environment:

$$\dot x = x(1-x)\big[g(\beta(\pi_C-\pi_D)) - g(\beta(\pi_D-\pi_C))\big],\qquad \dot n = \epsilon\, n(1-n)\big(-1 + (1+\theta)x\big),$$

with $\epsilon, \theta > 0$.

**Theorem (local stability).** The four corner equilibria are unstable (saddles). The interior equilibrium is stable if $\dfrac{P_1-S_1}{T_1-R_1} < \dfrac{S_0-P_0}{R_0-T_0}$ and unstable if the reverse strict inequality holds.

**Theorem (periodic orbits).** Write $\Delta(u) = g(\beta u) - g(-\beta u)$. If

$$\frac{P_1-S_1}{T_1-R_1} > \frac{S_0-P_0}{R_0-T_0}\quad\text{and}\quad \Delta(S_0-P_0)\,\Delta(T_1-R_1) > \Delta(S_1-P_1)\,\Delta(T_0-R_0),$$

then the system has a periodic orbit; it is a stable limit cycle (unstable interior equilibrium, repelling heteroclinic cycle on the boundary of the square). If both inequalities are reversed, there is an unstable limit cycle surrounding a stable interior equilibrium inside an attracting heteroclinic cycle.

For linear $g$ (the replicator time scale) $\Delta(u) \propto u$ and the second inequality becomes $\frac{S_0-P_0}{R_0-T_0} > \frac{P_1-S_1}{T_1-R_1}$, the reverse of the first, so both cannot hold and these limit cycles cannot arise; non-linear imitation breaks this degeneracy.

## Proof depends on

- [Poincaré–Bendixson theorem](../../../../../Dynamics/low-dimensional-dynamics/poincar-bendixson-theorem/poincare-bendixson.md)

## Expansion

The boundary of $[0,1]^2$ is a heteroclinic cycle through the four corners. Its stability is decided by the product of the ratios of contracting to expanding eigenvalues at the corners; at the corners $\dot x$ is governed by $\Delta$ evaluated at the pure-game payoff differences, giving the second inequality. When the interior equilibrium is a repeller and the heteroclinic cycle is also repelling, the Poincaré–Bendixson theorem on the invariant square yields an attracting periodic orbit, and symmetrically for the reversed case. With $g$ linear, $\Delta(u) \propto u$ and the two conditions coincide, so the classical model only shows neutral or degenerate oscillations at the threshold.

## Sources

- Yuan Liu, Lixuan Cao and Bin Wu, "General non-linear imitation leads to limit cycles in eco-evolutionary dynamics", Chaos, Solitons & Fractals 165 (2022), 112817, <https://doi.org/10.1016/j.chaos.2022.112817>; numbering as in arXiv:2210.10552: Equation (4), Theorems 1–2 and Corollaries 1–2.
