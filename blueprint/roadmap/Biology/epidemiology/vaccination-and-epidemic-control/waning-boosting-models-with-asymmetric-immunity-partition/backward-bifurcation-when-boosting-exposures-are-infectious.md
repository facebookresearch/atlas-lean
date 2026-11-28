# Backward bifurcation in a waning–boosting model when boosting exposures are infectious (SIRWJS)

**Model (SIRWJS).** Extend the SIRWS waning–boosting model by a compartment $J$ of secondary (sub-clinical) infections: exposure of a waning-immunity individual sends it to $J$ instead of directly to $R$, and $J$ individuals transmit with relative infectivity $\xi \ge 0$. With normalized population $S + I + R + W + J = 1$, transmission rate $\beta$, recovery rates $\gamma$ (primary) and $\rho$ (secondary), birth/death rate $\mu$, immune decay rate $\kappa$ partitioned by $\alpha, \omega > 1$ with $\alpha + \omega = \alpha\omega$ (full immunity lasts $1/(\alpha\kappa)$, waning immunity $1/(\omega\kappa)$), and boosting coefficient $\nu > 0$,

$$
\begin{aligned}
\dot S &= -\beta(I + \xi J)S + \omega\kappa W + \mu(1 - S), &
\dot I &= \beta(I + \xi J)S - (\gamma + \mu)I,\\
\dot R &= \gamma I - \alpha\kappa R + \rho J - \mu R, &
\dot W &= \alpha\kappa R - \omega\kappa W - \nu\beta(I + \xi J)W - \mu W,\\
\dot J &= \nu\beta(I + \xi J)W - (\rho + \mu)J .
\end{aligned}
$$

**Statement.** The basic reproduction number is $\mathcal{R}_0 = \beta/(\gamma + \mu)$ (secondary infections cannot occur at the disease-free state, where $W = 0$). Let $\eta = \alpha + \omega$ and

$$
Q_0 = \alpha\kappa\gamma, \qquad Q_1 = \bigl[(\gamma + \mu)(\eta\kappa + \mu) + \eta\kappa^2\bigr](\rho + \mu), \qquad \Theta = \nu\xi(\gamma + \mu)Q_0 - Q_1 .
$$

1. *Endemic equilibria.* Every non-negative equilibrium is epidemiologically feasible. For $\mathcal{R}_0 > 1$ there is exactly one endemic equilibrium besides the disease-free one.
2. *Subthreshold endemicity.* If $\Theta > 0$, there is $\tilde\beta \in (0, \gamma + \mu)$ such that for $\beta \in (\tilde\beta, \gamma + \mu)$ (i.e. $\tilde\beta/(\gamma+\mu) < \mathcal{R}_0 < 1$) there are two endemic equilibria besides the disease-free one, and for $\beta < \tilde\beta$ only the disease-free equilibrium. If $\Theta \le 0$, the disease-free equilibrium is the only feasible equilibrium for $\mathcal{R}_0 < 1$.
3. *Direction of bifurcation.* At $\mathcal{R}_0 = 1$ a transcritical bifurcation occurs, of backward type if $\Theta > 0$ and of forward type if $\Theta < 0$.
4. *Stability.* For $\mathcal{R}_0 > 1$ the endemic equilibrium is locally asymptotically stable iff the coefficients of its quartic characteristic polynomial $\lambda^4 + a_1\lambda^3 + a_2\lambda^2 + a_3\lambda + a_4$ satisfy $a_i > 0$, $a_1a_2 > a_3$ and $a_1a_2a_3 > a_1^2a_4 + a_3^2$.

Thus, when boosting exposures are themselves sufficiently infectious ($\nu\xi$ large relative to the immune-turnover term $Q_1/((\gamma+\mu)Q_0)$), the infection can persist below $\mathcal{R}_0 = 1$, so pushing $\mathcal{R}_0$ just below one need not eliminate it. With $\xi = 0$ the bifurcation is always forward and the model reduces, as $\rho \to \infty$, to the SIRWS model.

## Depends on

- [Endemic equilibrium and Routh–Hurwitz stability of the SIRWS model with asymmetric immunity partition](endemic-equilibrium-and-stability-of-the-sirws-model.md)

## Proof sketch

At an endemic equilibrium, the $I$ and $J$ equations give $J^*/I^* = (\gamma + \mu - \beta S^*)/(\beta\xi S^*) = \nu\beta W^*/(\rho + \mu - \nu\beta\xi W^*)$, so $S^* = (\gamma+\mu)/\beta - \nu\xi(\gamma+\mu)W^*/(\rho+\mu)$, and $I^*$, $J^*$ follow as functions of $W^*$. The remaining equation is a quadratic $f(W) = AW^2 + BW + C$ with $C = (\beta - \gamma - \mu)(\rho + \mu)^2 Q_0$, so $C > 0$ exactly when $\mathcal{R}_0 > 1$; feasibility confines $W^*$ to an explicit interval $(0, \overline W)$ on which $f$ changes sign once when $C > 0$. For $\mathcal{R}_0 < 1$ ($C < 0$), two positive roots require the linear coefficient to be positive near $\beta = \gamma + \mu$, where $B$ reduces to $\beta(\rho+\mu)\Theta$; this gives the threshold $\Theta$ and the saddle-node value $\tilde\beta$ where the discriminant vanishes. The direction of the transcritical bifurcation follows from the Castillo-Chavez–Song center-manifold coefficients at $\mathcal{R}_0 = 1$, whose sign is that of $\Theta$.

## Sources

- R. Opoku-Sarkodie, F.A. Bartha, M. Polner and G. Röst, "Bifurcation analysis of waning-boosting epidemiological models with repeat infections and varying immunity periods", *Mathematics and Computers in Simulation* 218 (2024), 624–643, <https://doi.org/10.1016/j.matcom.2023.12.006>. Preprint version: arXiv:2305.07947 (2023), Section 2 and Section 3, Lemma 1 and Theorems 1–3, <https://doi.org/10.48550/arXiv.2305.07947>.
