# Global dynamics of the SIR model with Preisach vaccination response

**Non-ideal relay.** For thresholds $\alpha = (\alpha_1, \alpha_2)$ with $\alpha_1 < \alpha_2$ and a continuous input $I(t)$, the relay state $\nu_\alpha(t) \in \{0,1\}$ switches to $1$ when $I$ reaches $\alpha_2$, switches to $0$ when $I$ reaches $\alpha_1$, and otherwise keeps its previous value (with $\nu_\alpha = 1$ whenever $I \ge \alpha_2$ and $\nu_\alpha = 0$ whenever $I \le \alpha_1$).

**Model.** With normalized densities $S + I + R = 1$, $\delta = \gamma + \mu > \mu$, consider

$$\dot I = \beta I S - \delta I, \qquad \dot S = -\beta I S - v(t) S - \mu S + \mu,$$

on $D = \{ I > 0, S > 0, S + I \le 1 \}$, where the vaccination rate is the output of a continuous Preisach operator,

$$v(t) = v_{\mathrm{nat}} + \iint_{\Pi} q(\alpha)\,\nu_\alpha(t)\,d\alpha_1\,d\alpha_2, \qquad \Pi = \{ 0 \le \alpha_1 < \alpha_2 \le 1 \},$$

with $q > 0$ bounded and measurable. Each threshold pair $\alpha$ labels a subpopulation (or an intervention policy) that raises vaccination when infection reaches $\alpha_2$ and stops when it falls to $\alpha_1$. The Preisach operator is globally Lipschitz, so the system defines a semiflow on triples $(I, S, \nu)$.

Let $\mathcal{R}_0 = \beta\mu / (\delta(\mu + v_{\mathrm{nat}}))$.

**Theorem.**
1. The infection-free equilibrium $(0, \mu/(\mu + v_{\mathrm{nat}}), \nu \equiv 0)$ is the global attractor if $\mathcal{R}_0 \le 1$.
2. If $\mathcal{R}_0 > 1$, the endemic equilibria form a connected continuum

$$I^* = \frac{\mu}{\delta} - \frac{\mu + v_0}{\beta}, \qquad S^* = \frac{\delta}{\beta}, \qquad v_0 = v_{\mathrm{nat}} + \iint_\Pi \nu_\alpha q(\alpha)\,d\alpha,$$

indexed by the relay states compatible with $I^*$; all share the same susceptible fraction $S^*$ but have different vaccination rates and infected fractions.
3. (Poincaré–Bendixson-type alternative.) If $\mathcal{R}_0 > 1$, every trajectory converges either to an endemic equilibrium or to a simple periodic orbit.
4. If $\mathcal{R}_0 > 1$, suppose every input–output loop of the Preisach operator for a simple periodic input is convex (ascending branch convex, descending branch concave), which holds for a uniform or nearly uniform density $q$, and that the relative loop width $L = \max_{I_1 < I_2} (I_2 - I_1)^{-1} \max_{I_1 \le I \le I_2} (\hat v(I) - \bar v(I))$ is sufficiently small. Then there are no periodic solutions and every trajectory converges to an endemic equilibrium.

## Expansion

Between switching moments the vaccination rate follows a single monotone branch $\tilde v(I)$ of the Preisach operator, so the trajectory solves a planar ODE with a Korobeinikov-type Lyapunov function

$$V(I,S) = S - S^*\ln\frac{S}{S^*} + I - I^*\ln\frac{I}{I^*} + \frac{1}{\beta}\int_{I^*}^{I} \frac{\tilde v(i) - \tilde v(I^*)}{i}\,di, \qquad \dot V = -\frac{\mu (S - S^*)^2}{S^* S} \le 0.$$

Trajectories crossing the nullcline $S = S^*$ only finitely often eventually stay on one branch and converge. For infinitely many crossings, the successive crossing points are compared arc by arc, which forces convergence to a simple periodic orbit along which the operator traces a hysteresis loop. Convexity of the loops makes the sublevel sets of the branch Lyapunov functions convex, and a small loop width bounds the jump $V_{u_1} - V_{u_2}$ incurred at each switch, which rules out the periodic orbit. With a single relay (perfectly homogeneous response) a stable endemic equilibrium can instead coexist with a stable periodic orbit, so heterogeneity of the behavioral response is what stabilizes the endemic state.

## Sources

- J. Kopfová, P. Nábělková, D. Rachinskii, S. C. Rouf, "Dynamics of SIR model with vaccination and heterogeneous behavioral response of individuals modeled by the Preisach operator", Journal of Mathematical Biology (2021), model (3), (7), (13), (24), equilibria (25)–(28), Proposition 1 with Lyapunov function (32)–(33), Theorem 1, assumption (A), loop width (22) and Theorem 2, <https://doi.org/10.1007/s00285-021-01629-8>, PMCID PMC8255057.
