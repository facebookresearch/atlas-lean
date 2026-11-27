# Integral control of the mean dimer count in a stochastic dimerization network

**Network.** Consider the stochastic mass-action reaction network

$$\varnothing \xrightarrow{k_1} S_1, \qquad S_1 + S_1 \xrightarrow{b} S_2, \qquad S_1 \xrightarrow{\gamma_1} \varnothing, \qquad S_2 \xrightarrow{\gamma_2} \varnothing,$$

a continuous-time Markov chain on $\mathbb Z_{\ge 0}^2$ for the copy numbers $(X_1, X_2)$, with positive constants $k_1, b, \gamma_1, \gamma_2$. The means $x_i = \mathbb E[X_i]$ obey the moment equations

$$\dot x_1 = k_1 + (b - \gamma_1) x_1 - b x_1^2 - b v, \qquad \dot x_2 = -\tfrac b2 x_1 - \gamma_2 x_2 + \tfrac b2 x_1^2 + \tfrac b2 v,$$

with $v = \operatorname{Var}(X_1)$, so the first moments are not closed: they depend on the variance.

**Ergodicity.** For all positive parameter values the network is exponentially ergodic, all its moments are bounded and converge exponentially fast, and $v(t) \to v^* \ge 0$ for every initial state.

**Controller.** The production rate is actuated by an integrator of the tracking error,

$$\dot I = \mu - x_2, \qquad k_1(t) = k_c \max\{0, I(t)\},$$

for a reference $\mu > 0$ and gain $k_c > 0$ (for every $\mu > 0$ some constant $k_1 > 0$ gives $\mathbb E[X_2]$ stationary mean $\mu$).

**Theorem (nominal stabilization).** Assume the stationary quantity $S^* = x_1^{*2} - x_1^* + v^*$ depends continuously on $k_1$. If

$$0 < k_c < 2\gamma_2 \Bigl(2\gamma_1 + \gamma_2 + 2\sqrt{\gamma_1(\gamma_1 + \gamma_2)}\Bigr),$$

the closed loop has a unique locally exponentially stable equilibrium $(x_1^*, x_2^*, I^*)$ in the positive orthant with $x_2^* = \mu$, and the stationary variance satisfies

$$v^* \in \Bigl(0, \frac{2\gamma_2 \mu}{b} + \frac14\Bigr].$$

**Theorem (robust stabilization).** If the parameters are only known to lie in a box $\gamma_1 \in [\gamma_1^-, \gamma_1^+]$, $\gamma_2 \in [\gamma_2^-, \gamma_2^+]$, $b \in [b^-, b^+]$ with positive endpoints, the same conclusion holds for every parameter in the box provided $0 < k_c < 2\gamma_2^-\bigl(2\gamma_1^- + \gamma_2^- + 2\sqrt{\gamma_1^-(\gamma_1^- + \gamma_2^-)}\bigr)$, with $v^* \in (0, 2\gamma_2^+\mu/b^- + 1/4]$.

## Depends on

- [The integral-feedback loop as a linear system and its equilibrium](../../integral-feedback-and-perfect-adaptation/the-integral-feedback-loop-as-a-linear-system-and-its-equilibrium.md)

## Proof sketch

Ergodicity and moment convergence come from a Foster-Lyapunov drift condition with a linear function $V(x) = \nu^\top x$: dimerization removes two $S_1$ and creates one $S_2$, so quadratic terms in $LV$ have a favourable sign and the drift is bounded by $c_1 - c_2 V$. At equilibrium the integrator forces $x_2^* = \mu$; eliminating $v^*$ between the two moment equations gives $k_1^* = \gamma_1 x_1^* + 2\gamma_2\mu$, and positivity of $v^*$ yields the explicit variance window. Local stability is checked on the linearization with the variance treated as an exogenous input frozen at $v^*$ (the worst case), whose characteristic polynomial is cubic; the Routh-Hurwitz conditions reduce to the stated bound on $k_c$. A naive linear model that drops the quadratic and variance terms would wrongly predict that integral control cannot stabilize this network, because its closed-loop matrix has positive determinant.

## Sources

- Corentin Briat and Mustafa Khammash, "Integral population control of a quadratic dimerization process", in *52nd IEEE Conference on Decision and Control*, IEEE, 2013, 3367–3372, <https://doi.org/10.1109/cdc.2013.6760398>. Preprint version: arXiv:1307.6446 (2013), Proposition 1, Theorem 2, Assumption 3, Proposition 4, Theorem 5 and Theorem 6, Remark 7, <https://doi.org/10.48550/arXiv.1307.6446>.
