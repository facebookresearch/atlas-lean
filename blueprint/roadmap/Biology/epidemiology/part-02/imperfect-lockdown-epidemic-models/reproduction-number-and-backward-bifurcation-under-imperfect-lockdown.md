# Reproduction number and backward bifurcation under imperfect lockdown

**Model.** Let susceptibles $S$, locked-down susceptibles $L$, exposed $E$, un-notified infectious $I$, hospitalized or isolated $J$ and recovered $R$ have total $N$. Recruitment is $\Pi > 0$, natural mortality $\mu > 0$, susceptibles enter lockdown at rate $l > 0$ and leave it at rate $\psi > 0$, the lockdown efficacy parameter $r \in (0, 1)$ is the relative susceptibility of locked-down individuals, and isolated individuals do not mix, so the force of infection is $\lambda = \beta I / (N - J)$:

$$\begin{aligned}
S' &= \Pi + \psi L - \lambda S - (\mu + l) S, & L' &= l S - r\lambda L - (\mu + \psi) L,\\
E' &= \lambda (S + r L) - (\gamma + \mu) E, & I' &= \gamma E - (\eta + \tau_1 + \mu) I,\\
J' &= \eta I - (\tau_2 + \delta + \mu) J, & R' &= \tau_1 I + \tau_2 J - \mu R .
\end{aligned}$$

The region $\{N \le \Pi / \mu\}$ of $\mathbb{R}^6_{\ge 0}$ is positively invariant and attracting.

**Disease-free equilibrium and threshold.** The disease-free equilibrium is

$$S_0 = \frac{\Pi (\mu + \psi)}{\mu (\mu + \psi + l)}, \qquad L_0 = \frac{\Pi l}{\mu (\mu + \psi + l)},$$

and the next-generation matrix gives

$$\mathcal{R}_0 = \frac{\beta \gamma\, (\mu + \psi + r l)}{(\mu + \gamma)(\eta + \tau_1 + \mu)(\mu + \psi + l)} .$$

The disease-free equilibrium is locally asymptotically stable if $\mathcal{R}_0 < 1$ and unstable if $\mathcal{R}_0 > 1$. Since $\partial \mathcal{R}_0 / \partial l = -\mathcal{R}_0 (1 - r)/(\mu + \psi + rl) \cdot (\mu + \psi)/(\mu + \psi + l) < 0$ for $r < 1$, faster lockdown always lowers the threshold, down to the factor $r$ as $l \to \infty$.

**Endemic equilibria.** Every endemic equilibrium is determined by its force of infection $\lambda^\ast > 0$, which solves a quadratic

$$A (\lambda^\ast)^2 + B \lambda^\ast + C = 0, \qquad A > 0, \qquad C = \mu k_3 k_4 k_5 (k_2 + l)(1 - \mathcal{R}_0),$$

with $k_2 = \mu + \psi$, $k_3 = \gamma + \mu$, $k_4 = \eta + \tau_1 + \mu$, $k_5 = \tau_2 + \delta + \mu$. Hence there is a unique endemic equilibrium when $\mathcal{R}_0 > 1$ ($C < 0$). When $\mathcal{R}_0 = 1$ ($C = 0$) there is one if $B < 0$ and none if $B \ge 0$. When $\mathcal{R}_0 < 1$ ($C > 0$) there are two endemic equilibria if $B < 0$ and $B^2 - 4AC > 0$, exactly one (a double root) if $B < 0$ and $B^2 = 4AC$, and none if $B \ge 0$, or if $B < 0$ and $B^2 < 4AC$.

**Backward bifurcation.** Two endemic equilibria for $\mathcal{R}_0 < 1$ only indicate that a backward bifurcation is possible. With $\beta$ as bifurcation parameter, the coefficient $b$ of the [Castillo-Chavez–Song theorem](../../part-01/backward-bifurcation/castillo-chavez-song-centre-manifold-bifurcation-theorem.md) at $\mathcal{R}_0 = 1$ is always positive, so the system undergoes a backward bifurcation at $\mathcal{R}_0 = 1$ whenever its coefficient $a$ is positive: a positive, unstable endemic equilibrium then exists for $\mathcal{R}_0$ slightly below $1$. The coefficient $a$ is nonlinear in $r$ (via $\beta^*$ and $w$, with $a < 0$ at both $r = 0$ and $r = 1$, and the right-hand side of the source's (3.14) depending on $r$) and negative at $r = 0$, so there is no backward bifurcation when locked-down individuals cannot be infected; the source writes $a > 0$ as an explicit lower bound on $r$. The source shows only numerically that a stable endemic state can then coexist with the stable disease-free state for $\mathcal{R}_0 < 1$, in which case bringing $\mathcal{R}_0$ below one does not by itself guarantee elimination.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Quadratic endemic-equilibrium condition for backward bifurcation](../../part-01/backward-bifurcation/quadratic-endemic-equilibrium-condition-for-backward-bifurcation.md)
- [Castillo-Chavez–Song centre-manifold bifurcation theorem](../../part-01/backward-bifurcation/castillo-chavez-song-centre-manifold-bifurcation-theorem.md)

## Expansion

At the disease-free equilibrium $N_0 = \Pi / \mu$, and one infectious individual generates new exposures at rate $\beta (S_0 + r L_0)/N_0 = \beta (\mu + \psi + rl)/(\mu + \psi + l)$; multiplying by the probability $\gamma / (\gamma + \mu)$ of surviving the latent period and the mean infectious time $1/(\eta + \tau_1 + \mu)$ before notification, recovery or death gives $\mathcal{R}_0$ (the isolated class does not transmit, so it does not contribute). Setting the derivatives to zero expresses every equilibrium coordinate in terms of $\lambda^\ast$, and substituting into $\lambda^\ast = \beta I^\ast/(N^\ast - J^\ast)$ yields the quadratic. Whether $B < 0$ can hold with $C > 0$ depends on the parameters. The centre-manifold coefficients are computed from the left and right null vectors $v, w$ of the Jacobian at the disease-free equilibrium at $\mathcal{R}_0 = 1$: $b = v_3 w_4 (\mu + \psi + r l)/(\mu + \psi + l) > 0$ with $v_3, w_4 > 0$, since $\partial^2 f_E/\partial I\,\partial\beta = (S_0 + r L_0)/N_0$ at the disease-free equilibrium. The coefficient $a$ is a positive multiple of an expression nonlinear in $r$ (via $\beta^*$ and $w$, with $a < 0$ at both $r = 0$ and $r = 1$, and the right-hand side of the source's (3.14) depending on $r$) that is negative at $r = 0$ (the null vector component $w_1$ is negative), so the backward bifurcation comes from infection during lockdown ($r > 0$); the paper exhibits it numerically. With $r = 1$ (lockdown confers no protection) $\mathcal{R}_0$ no longer depends on $l$.

## Sources

- S. S. Nadim, J. Chattopadhyay, "Occurrence of backward bifurcation and prediction of disease transmission with imperfect lockdown: a case study on COVID-19", Chaos, Solitons & Fractals 140 (2020) 110163, Section 2 (model (2.1)), Section 3 (Theorem 3.1, Equation (3.2), Lemma 3.1, Equations (3.4)–(3.6), Theorem 3.2; Section 3.4 with Equations (3.12)–(3.14) and Theorem 3.3), <https://doi.org/10.1016/j.chaos.2020.110163> (PMC7430254).
