# Ecological reproduction number of a vector-borne SIR-SI model with Lotka-Volterra predation

**Model.** Hosts $S_h, I_h, R_h$ (constant total $N_h$), vectors $S_v, I_v$ and a predator $D$ of the vectors satisfy

$$ \dot S_h = \mu_h N_h - \frac{b \beta_h}{N_h} S_h I_v - \mu_h S_h, \qquad \dot I_h = \frac{b \beta_h}{N_h} S_h I_v - (\gamma + \mu_h) I_h, $$

$$ \dot S_v = \mu_v (S_v + I_v) - \Bigl( \frac{b \beta_v}{N_h} I_h + \alpha D \Bigr) S_v, \qquad \dot I_v = \frac{b \beta_v}{N_h} S_v I_h - \alpha D I_v, \qquad \dot D = \eta (S_v + I_v) D - \mu_D D, $$

with biting rate $b$, transmission probabilities $\beta_h, \beta_v$, recovery $\gamma$, host turnover $\mu_h$, vector birth rate $\mu_v$, predation rate $\alpha$, conversion $\eta$ and predator death $\mu_D$. The total vector population $N_v = S_v + I_v$ and $D$ form a classical Lotka-Volterra system $\dot N_v = (\mu_v - \alpha D) N_v$, $\dot D = (\eta N_v - \mu_D) D$. After rescaling time by $\mu_v$, host classes by $N_h$, vectors by $\mu_D/\eta$ and predators by $\mu_v/\alpha$, with $B_h = \frac{b \beta_h \mu_D}{\mu_v N_h \eta}$, $B_v = \frac{b \beta_v}{\mu_v}$ and rescaled rates $\hat\gamma = \gamma/\mu_v$, $\hat\mu_h = \mu_h/\mu_v$, the Lotka-Volterra orbits are the level sets of the conserved quantity $V_{LV}(N_v, D) = \ln N_v - N_v + \ln D - D \le -2$, with equality only at the coexistence point $(1,1)$.

**Results.**

1. Solutions with nonnegative initial data are nonnegative, bounded and global.
2. With $R_0 = \sqrt{B_h B_v / (\hat\gamma + \hat\mu_h)}$, the next-generation spectral radius at the nontrivial disease-free equilibrium $E_2$ (vectors and predators at coexistence), the trivial disease-free equilibrium $E_1$ is unstable; $E_2$ is unstable if $R_0 > 1$; if $R_0 < 1$, infections starting near $E_2$ die out, and $E_1, E_2$ are the only equilibria.
3. (Ecological reproduction number) For $k_0 < -2$ the set $\Omega^+_{k_0} = \{ S_h + I_h \le 1,\ V_{LV}(S_v + I_v, D) \le k_0 \}$ is compact and positively invariant, and on it $0 < a(k_0) \le N_v, D \le b(k_0)$. Define

$$ R_0(k_0) = \frac{B_h B_v}{\hat\gamma + \hat\mu_h} \cdot \frac{b(k_0)}{a(k_0)} > R_0^2. $$

If $R_0(k_0) < 1$, then $E_2$ is stable in $\Omega^+_{k_0}$ and $I_h, I_v \to 0$ for all solutions in $\Omega^+_{k_0}$.

Since $b(k_0)/a(k_0) \to \infty$ as $k_0 \to -\infty$, large predator-prey oscillations, which bring high vector peaks and low predator troughs, defeat natural biological control even when $R_0 < 1$. When natural control is insufficient, predator releases $u(t) \in [0, u_{\max}]$ maximizing $\int_0^T (-c u^2 - q u - r I_h)\, dt + a S_h(T)$ admit an optimal control, characterized by Pontryagin's maximum principle.

## Expansion

Positivity follows because the infected subsystem is cooperative given nonnegative inputs, and boundedness because $(N_v, D)$ moves on a closed Lotka-Volterra orbit while $S_h + I_h \le N_h$. The equilibrium $E_2$ is not hyperbolic in the ecological directions (the Lotka-Volterra center), so linearization only controls the infected compartments locally. For the global statement, on $\Omega^+_{k_0}$ one has $\dot I_h \le B_h I_v - (\hat\gamma + \hat\mu_h) I_h$ and $\dot I_v \le B_v b(k_0) I_h - a(k_0) I_v$; the comparison matrix of this cooperative linear system is Hurwitz exactly when $(\hat\gamma + \hat\mu_h) a(k_0) - B_h B_v b(k_0) > 0$, that is $R_0(k_0) < 1$, so $(I_h, I_v) \to 0$. Existence of an optimal release follows from Filippov-Cesari type conditions: bounded states, compact convex control set, and an integrand convex in $u$.

## Sources

- Rocio Balderrama, Ignacio Ceresa Dussel, Constanza Sanchez de la Vega, "Optimal Control Strategies for Epidemic Dynamics: Integrating SIR-SI and Lotka--Volterra Models", arXiv (2026). Section 2 (model), Section 3 (positivity, local and global stability propositions, $R_0(k_0)$), Section 4 (existence of an optimal control and necessary conditions). <https://doi.org/10.48550/arXiv.2602.06178>
