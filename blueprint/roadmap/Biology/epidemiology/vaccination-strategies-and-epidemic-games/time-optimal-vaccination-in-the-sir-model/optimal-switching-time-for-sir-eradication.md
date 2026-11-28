# Optimal switching time for minimum-time SIR vaccination

Setting: the vaccination-controlled SIR system $\dot S = -\beta S I - r S$, $\dot I = \beta S I - \gamma I$ with $\beta, \gamma > 0$, controls $r(t) \in [0,1]$, threshold $\mu > 0$, eradication time $u^r(x,y) = \inf\{t > 0 : I^r(t) = \mu\}$ from $S(0) = x \ge 0$, $I(0) = y \ge \mu$, and value function $u = \min_r u^r$. Every optimal vaccination rate is a single bang-bang switch

$$r_\tau(t) = \begin{cases} 0, & t \in [0,\tau], \\ 1, & t > \tau, \end{cases}$$

for some $\tau \ge 0$ (no vaccination, then maximal vaccination). Write $u^{r_0}$ for the eradication time under constant maximal vaccination.

**Theorem (optimal stopping representation).** Let $(S, I)$ solve the uncontrolled SIR system $\dot S = -\beta S I$, $\dot I = \beta S I - \gamma I$ with $S(0) = x \ge 0$, $I(0) = y \ge \mu$. Then

$$u(x,y) = \min_{\tau \ge 0} \bigl\{ \tau + u^{r_0}(S(\tau), I(\tau)) \bigr\},$$

any minimizing $\tau$ gives an optimal vaccination rate $r_\tau$, and

$$\tau^* = \min\{ t \ge 0 : u(S(t), I(t)) = u^{r_0}(S(t), I(t)) \}$$

is a minimizing time. Consequently $u$ is a viscosity solution of the obstacle (free-boundary) problem

$$\max\bigl\{ \beta x y\, \partial_x u + (\gamma - \beta x) y\, \partial_y u - 1,\ u - u^{r_0} \bigr\} = 0 \quad \text{in } (0,\infty) \times (\mu,\infty),$$

and $\tau^*$ is the first entrance time of the uncontrolled trajectory into the stopping region $\mathcal{S} = \{ u = u^{r_0} \}$. In the interior of $\mathcal{S}$, $\partial_x u \ge 0$, while $\partial_x u \le 0$ almost everywhere in $\mathcal{S}^c$.

**Pontryagin conditions from the value function.** If $x > 0$, $y > \mu$ and $r$ is optimal with $u(x,y) = u^r(x,y)$, then $P(t) = \partial_x u^r(S^r(t), I^r(t))$ and $Q(t) = \partial_y u^r(S^r(t), I^r(t))$ solve the adjoint system

$$\dot P = (\beta I^r + r) P - \beta I^r Q, \qquad \dot Q = \beta S^r P + (\gamma - \beta S^r) Q,$$

and satisfy $r(t) P(t) = P(t)^+$ for a.e. $t$ and $\beta S^r I^r P + S^r P^+ + (\gamma - \beta S^r) I^r Q = 1$ on $[0, u(x,y)]$, i.e. the necessary conditions of the maximum principle hold with explicit multipliers.

## Depends on

- [Value function of the SIR eradication-time problem](eradication-time-value-function-hjb.md)

## Expansion

Because optimal controls are of the form $r_\tau$, $u(x,y) = \min_{0 \le \tau \le u(x,y)} u^{r_\tau}(x,y)$, and before time $\tau$ the controlled trajectory coincides with the uncontrolled SIR trajectory, so $u^{r_\tau}(x,y) = \tau + u^{r_0}(S(\tau), I(\tau))$. This converts the control problem into an optimal stopping problem along a single SIR orbit: one waits (letting natural infection deplete susceptibles) until the value of vaccinating at full rate equals the optimum. The dynamic programming principle then yields the obstacle equation, the stopping set being where the obstacle $u^{r_0}$ is active. The adjoint identities follow by differentiating $u^r$ along the trajectory using the $C^1$ regularity of $u^r$ and the HJB equation along optimal paths.

## Sources

- Ryan Hynd, Dennis Ikpe, Terrance Pendleton, "An eradication time problem for the SIR model", arXiv (2020). Theorem 1.4, Theorem 1.6, Corollary 6.3, Corollary 6.4, Proposition 7.1, Lemma 7.2 (the bang-bang structure is attributed there to Bolzoni, Bonacini, Soresina and Groppi). <https://doi.org/10.48550/arXiv.2008.12744> Published version: Journal of Differential Equations 303 (2021) 214–252, <https://doi.org/10.1016/j.jde.2021.09.001>.
