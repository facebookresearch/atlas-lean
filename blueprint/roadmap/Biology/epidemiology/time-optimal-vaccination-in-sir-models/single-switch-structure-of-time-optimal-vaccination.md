# Single-switch structure of time-optimal vaccination in a state-dependent SIR model

Consider the controlled SIR model on $\Omega = \{(S,I) \in (0,1]^2 : S + I \le 1\}$,

$$
\dot S = -\beta(S,I)\,S I - u(t)\,S, \qquad \dot I = \beta(S,I)\,S I - \gamma(S,I)\,I, \qquad u(t) \in [0,1],
$$

where $S, I$ are susceptible and infected fractions and $u$ is the vaccination effort. Assume (A1) $\beta, \gamma$ extend to positive $C^1$ functions on a neighbourhood of $\overline\Omega$; (A2) $S(0) > 0$, $I(0) > 0$, $S(0) + I(0) \le 1$; (A3) $\beta + I\,\partial_I \beta > 0$ on $\Omega$; and the structural sign condition

$$
G(S,I) = \beta + S\,\partial_S \beta - \partial_S \gamma > 0 \quad \text{on } \Omega ,
$$

i.e. the per-capita growth rate $\beta S - \gamma$ increases strictly with $S$. For a threshold $\varepsilon > 0$ with $I(0) > \varepsilon$, minimize the eradication time $T = \inf\{t \ge 0 : I(t) \le \varepsilon\}$ over measurable controls.

**Theorem.** Every optimal control is bang-bang with at most one switch, from no vaccination to full vaccination: there is $\tau^* \in [0, T^*]$ with $u^*(t) = 0$ for a.e. $t < \tau^*$ and $u^*(t) = 1$ for a.e. $t > \tau^*$. Equivalently, the minimum-time value function satisfies

$$
V(S,I) = \inf_{\tau \ge 0} \big\{ \tau + W(\Phi^0_\tau(S,I)) \big\},
$$

where $\Phi^0$ is the uncontrolled flow ($u \equiv 0$) and $W$ is the eradication time under $u \equiv 1$; the earliest optimal switch time is the first $t$ with $V(\Phi^0_t(z)) = W(\Phi^0_t(z))$.

## Expansion

The Hamiltonian is affine in $u$ with switching function proportional to $-\lambda_S S$, where $\lambda_S$ is the costate of $S$; normality ($\lambda_0 > 0$) holds under the assumptions. Differentiating the switching function along extremals produces a factor of $G$, so under $G > 0$ the switching function can cross zero at most once and only in the direction that turns vaccination on. Waiting before vaccinating is optimal because early on infection itself depletes susceptibles; later, removing susceptibles shortens the time for prevalence to fall below $\varepsilon$. Outside the regime $G > 0$ the paper exhibits numerical examples with other structures.

## Sources

- Yeachan Park, Jiwoong Jang and Yeoneung Kim, *Time-optimal vaccination in state-dependent SIR models: a single switch criterion and numerical examples outside its regime*, arXiv:2610.23095, Theorem 1 and Proposition 1 (Section 3), Theorem 3 and Corollary 3 (Section 5). <https://doi.org/10.48550/arXiv.2610.23095>
