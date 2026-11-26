# Pheromone threshold for pest eradication under mating disruption and trapping

**Model.** In the mating-structured pest model (immatures $I$, unmated females $Y$, mated females $F$, males $M$) add pheromone lures equivalent to $Y_P > 0$ virtual females. A male is attracted to wild females with probability $Y/(Y+Y_P)$ and to lures with probability $Y_P/(Y+Y_P)$; lured males are killed or captured at rate $\alpha \ge 0$:

$$ \dot I = b\Big(1-\frac IK\Big)F - (\nu_I+\mu_I)I, \quad \dot Y = r\nu_I I - \nu_Y \min\Big\{\frac{\gamma M}{Y+Y_P},1\Big\} Y + \delta F - \mu_Y Y, \quad \dot F = \nu_Y \min\Big\{\frac{\gamma M}{Y+Y_P},1\Big\} Y - (\delta+\mu_F)F, \quad \dot M = (1-r)\nu_I I - \Big(\mu_M + \alpha\frac{Y_P}{Y+Y_P}\Big)M. $$

Assume the uncontrolled population is established in the male-abundance regime: $\mathcal N_0 > 1$ and $Y^* < \gamma M^*$, where $EE^* = (I^*,Y^*,F^*,M^*)$ is the uncontrolled positive equilibrium. Set

$$ Y_P^* = \frac{\gamma M^* - Y^*}{1 + \alpha/\mu_M}. $$

**Theorem (equilibria under control).** For every $Y_P > 0$ the trivial equilibrium $TE$ is asymptotically stable (the control creates a strong Allee effect). There is a threshold $Y_P^{**} > Y_P^*$ such that:

1. if $0 < Y_P < Y_P^*$ there are two positive equilibria, a lower one $EE^{(1)}_{MD}$ and $EE^\# = (I^*,Y^*,F^*,M^\#)$, which is asymptotically stable and has only the male class reduced: $M^\# = M^*/\big(1 + \alpha Y_P/(\mu_M(Y^*+Y_P))\big)$;
2. if $Y_P^* < Y_P < Y_P^{**}$ there are two positive equilibria $EE^{(1)}_{MD}$ and $EE^{(2)}_{MD}$, both in the male-scarcity region;
3. if $Y_P > Y_P^{**}$ there is no positive equilibrium.

**Theorem (global eradication).** There is a computable threshold $\tilde Y_P^{**} \ge Y_P^{**}$, the value of $Y_P$ at which a line through $(K,0)$ with slope proportional to $Y_P$ becomes tangent to a fixed cubic, such that:

1. if $Y_P > \tilde Y_P^{**}$, $TE$ is globally asymptotically stable on $\mathbb R^4_+$, so any established or invading population is eliminated;
2. if $0 < Y_P \le \tilde Y_P^{**}$, the basin of attraction of $TE$ contains the order interval $\{x \in \mathbb R^4_+ : x < \tilde E^{(1)}\}$ below the lower equilibrium $\tilde E^{(1)}$ of the comparison system.

## Expansion

Below $Y_P^*$ the lures do not push the established equilibrium out of male abundance, so mating is unaffected and only the males are depleted. Between the thresholds the population persists but in a male-scarcity state. Lowering it further only becomes possible once a positive equilibrium no longer exists. The full system is not monotone, because of the term $-\nu_Y\gamma M Y/(Y+Y_P)$ in $\dot Y$. The proof bounds it above by a cooperative comparison system: drop that term from $\dot Y$ and use $\gamma M/(Y+Y_P)$ in place of the minimum in $\dot F$. That system's positive equilibria are the intersections of the line $\eta(Y_P,\cdot)$ with a cubic $\tilde\psi(I)$ on $[0,I_1]$, and these disappear once $Y_P > \tilde Y_P^{**}$. Comparison and monotone convergence then force every solution of the original model to $0$. With the parameter set used in the paper, raising the capture rate from $\alpha = 0$ to $\alpha = 0.1$ cuts both $Y_P^*$ and $Y_P^{**}$ by about $90\%$. This is why mating disruption works much better combined with trapping.

## Depends on

- [Basic offspring number of a mating-structured insect pest model](basic-offspring-number-of-a-mating-structured-insect-pest-model.md)

## Sources

- Roumen Anguelov, Claire Dufourd, Yves Dumont, "Mathematical model for pest-insect control using mating disruption and trapping", arXiv:1608.04880 (2016): Section 3, Theorem 4 (equilibrium $EE^\#$ under male abundance), Theorem 5 (male scarcity), Theorem 6 (equilibria of the controlled model), Theorem 7 (comparison system) and Theorem 8 (global asymptotic stability of the trivial equilibrium); numerical thresholds in Section 4. <https://doi.org/10.48550/arXiv.1608.04880> Published version: Applied Mathematical Modelling 52 (2017), 437-457, <https://doi.org/10.1016/j.apm.2017.07.060>.
