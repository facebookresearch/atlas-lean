# Equilibria and delay-induced tipping in a two-polymerase quasispecies model

**Model.** Master genomes $x_0$ and mutant genomes $x_1$ encode polymerases $p_0$ and $p_1$, which become functional after delays $\tau_0, \tau_1$:
$$\begin{aligned}
\dot x_0 &= (1-\mu)\gamma\, x_0\, \bigl[r_0 p_0(t-\tau_0) + r_1 p_1(t-\tau_1)\bigr]\,(1 - x_0 - x_1) - \varepsilon x_0,\\
\dot x_1 &= \bigl(\mu\gamma\, x_0 + (1-\gamma) x_1\bigr)\bigl[r_0 p_0(t-\tau_0) + r_1 p_1(t-\tau_1)\bigr]\,(1 - x_0 - x_1) - \varepsilon x_1,\\
\dot p_0 &= k_0 x_0 (1 - p_0 - p_1) - \varepsilon_p p_0, \qquad \dot p_1 = k_1 x_1 (1 - p_0 - p_1) - \varepsilon_p p_1,
\end{aligned}$$
with mutation rate $\mu$ (no back mutation), polymerase affinity fraction $\gamma$ for master genomes, replication rates $r_i$, polymerase synthesis rates $k_i$ and degradation rates $\varepsilon, \varepsilon_p$, on a bounded region $\mathcal D$ of densities.

**Theorem.**
1. The hyperplane $\mathcal A = \{\gamma\mu x_0 + (1 + \gamma(\mu - 2)) x_1 = 0\}$ is invariant, also for the delay system (histories in $C([-\tau, 0], \mathcal A)$, $\tau = \max \tau_i$).
2. The extinction equilibrium is always a local sink. Explicit parameter conditions place the remaining equilibria in $\mathcal D$: two equilibria $\mathbf x_2^*, \mathbf x_3^*$, and two master–mutant coexistence equilibria $\mathbf x_4^*, \mathbf x_5^*$.
3. For $\varepsilon$ small, $\mathbf x_4^*$ and $\mathbf x_5^*$ are asymptotically stable whenever they lie in $\mathcal D$; $\mathbf x_2^*, \mathbf x_3^*$ are asymptotically stable if $\gamma < (2 - \mu)^{-1}$ and unstable if $\gamma > (2 - \mu)^{-1}$.
4. Without delays ($\tau_0 = \tau_1 = 0$, $\varepsilon_p = \varepsilon$, $0 < \mu, \gamma < 1$) there are no nonconstant periodic orbits in $\mathcal D$, so bounded trajectories converge to equilibria; the equilibria are unchanged by delays.

Transitions between coexistence, mutant-only persistence (error catastrophe) and extinction occur through transcritical and saddle-node bifurcations; delays leave equilibria fixed but reshape their basins, so that increasing $\tau$ can send populations that would persist to extinction ($\tau$-tipping).

## Depends on

- [Eigen's error threshold](../eigen-s-quasispecies-error-threshold/master-equilibrium-exp-pos-iff.md)

## Expansion

Because both genome classes need polymerase to replicate, the origin is stable: a population too small to make enough polymerase cannot recover, which creates bistability with the persistent states. Delays in polymerase activation mean the replication term responds to past genome densities; after a perturbation the polymerase pool lags behind, and trajectories can cross the separatrix into the extinction basin. When mutants encode a functional polymerase ($k_1 > 0$) loss of the master leads to mutant replacement; in the complementation limit where mutants rely on master-derived polymerase, loss of the master leads to complete extinction.

## Sources

- E. A. Turner, F. Crespo, N. Morales, S. F. Elena, "Polymerase-mediated quasispecies dynamics: bifurcations, complementation, and robustness of τ-tipping", arXiv:2609.13310 (2026), Propositions 1, 2, 3, 4 and 5, Theorems 1 and 2, <https://doi.org/10.48550/arXiv.2609.13310>.
