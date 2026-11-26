# Steady states and stability of the three-compartment hematopoiesis model

**Model.** Let $u_1, u_2, u_3 \ge 0$ be the numbers of stem, progenitor and mature white blood cells. Stage $i \in \{1,2\}$ proliferates at rate $p_i > 0$ with maximal self-renewal fraction $a_i \in (0,1)$, mature cells die at rate $d_3 > 0$, and self-renewal is down-regulated by the feedback signal $1/(1 + k u_3)$, $k > 0$:

$$\frac{du_1}{dt} = \Big(\frac{2a_1}{1 + k u_3} - 1\Big) p_1 u_1,$$

$$\frac{du_2}{dt} = \Big(\frac{2a_2}{1 + k u_3} - 1\Big) p_2 u_2 + 2\Big(1 - \frac{a_1}{1 + k u_3}\Big) p_1 u_1,$$

$$\frac{du_3}{dt} = 2\Big(1 - \frac{a_2}{1 + k u_3}\Big) p_2 u_2 - d_3 u_3.$$

**Proposition (equilibria and boundedness).** Solutions with positive initial data stay in the open first octant and eventually enter a compact set independent of the initial data. The nonnegative steady states are:

- $E_0 = (0,0,0)$, for all parameters; it is locally asymptotically stable if $\max\{a_1, a_2\} < \tfrac12$ and unstable if $\max\{a_1,a_2\} > \tfrac12$;
- $E_1 = \big(0, \tfrac{d_3}{p_2}\bar u_3^1, \bar u_3^1\big)$ with $\bar u_3^1 = (2a_2 - 1)/k$, which exists with positive components iff $a_2 > \tfrac12$; it is locally asymptotically stable if $a_1 < a_2$ and unstable if $a_1 > a_2$;
- the positive state $E_2 = (\bar u_1, \bar u_2, \bar u_3)$ with

$$\bar u_3 = \frac{2a_1 - 1}{k}, \qquad \bar u_2 = \frac{d_3 \, \bar u_3}{(2 - a_2/a_1)\, p_2}, \qquad \bar u_1 = \Big(1 - \frac{a_2}{a_1}\Big) \frac{p_2}{p_1} \bar u_2,$$

which exists iff $a_1 > \tfrac12$ and $a_2 < a_1$.

**Theorem (stability of the positive state).** Let $a_1 > \tfrac12$, $a_2 < a_1$, and set

$$\beta = 1 - \frac{a_2}{a_1}\Big(1 - \frac{1}{2a_1}\Big)\frac{1}{2 - a_2/a_1}, \qquad \gamma = \frac{1}{2a_1}\,\frac{1}{1 - \frac{1}{2a_1}} + \frac{a_2}{a_1}\,\frac{1}{(2 - a_2/a_1)(1 - a_2/a_1)},$$

$$p_2^* = \frac{p_1}{1 - a_2/a_1}\Big[\frac{1}{\gamma} - \beta \frac{d_3}{p_1}\Big].$$

Then $E_2$ is locally asymptotically stable if $p_2 > p_2^*$ and unstable if $p_2 < p_2^*$. Consequently $E_2$ exists and is locally asymptotically stable iff $a_1 > \tfrac12$, $a_1 > a_2$ and $p_2 > p_2^*$, and in that case every other nonnegative steady state is unstable.

## Expansion

At a steady state with $u_1 > 0$ the first equation forces $1 + k u_3 = 2a_1$, which fixes $\bar u_3$; the remaining two equations are then linear in $u_1, u_2$. The stability condition is the Routh–Hurwitz inequality $c_1 c_2 > c_3$ for the cubic characteristic polynomial $\lambda^3 + c_1\lambda^2 + c_2\lambda + c_3$ of the Jacobian at $E_2$; after transforming back to the model parameters, $c_1 c_2 - c_3 > 0$ is exactly $p_2 > p_2^*$. Slow progenitor proliferation (small $p_2$) therefore destabilizes the positive state. In the two-compartment version of the model the positive state is globally stable whenever it exists, so instability is created by the intermediate stage.

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)
- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- F. Knauer, T. Stiehl and A. Marciniak-Czochra, "Oscillations in a white blood cell production model with multiple differentiation stages", arXiv:1812.02017 (2018), model (M1)–(M3), Theorem 1, Propositions 2–3, Theorem 4 and Corollary 6, <https://doi.org/10.48550/arXiv.1812.02017>.
