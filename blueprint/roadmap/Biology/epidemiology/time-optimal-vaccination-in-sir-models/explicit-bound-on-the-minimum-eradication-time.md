# Explicit bound on the minimum eradication time under vaccination

In the controlled SIR model $\dot S = -\beta(S,I)SI - uS$, $\dot I = \beta(S,I)SI - \gamma(S,I)I$ with $u(t) \in [0,1]$ on $\Omega = \{(S,I) \in (0,1]^2 : S+I \le 1\}$, with $\beta, \gamma$ positive and $C^1$ on a neighbourhood of $\overline\Omega$ and $\beta + I\partial_I\beta > 0$, put

$$
\beta_{\max} = \sup_{\Omega} \beta, \qquad \gamma_{\min} = \inf_{\Omega} \gamma ,
$$

and let $T^*(S_0, I_0, \varepsilon)$ be the minimum time for prevalence to reach $I \le \varepsilon$ from $(S_0, I_0) \in \Omega$ with $I_0 > \varepsilon$.

**Theorem.** With $t_c = \max\{0, \ln(2\beta_{\max} S_0/\gamma_{\min})\}$,

$$
T^*(S_0, I_0, \varepsilon) \le t_c + \frac{2}{\gamma_{\min}} \Big[ \beta_{\max} S_0\, t_c + \ln\frac{I_0}{\varepsilon} \Big] < \infty .
$$

In the subcritical regime $\beta_{\max} S_0 < \gamma_{\min}$,

$$
T^*(S_0, I_0, \varepsilon) \le \frac{1}{\gamma_{\min} - \beta_{\max} S_0} \ln\frac{I_0}{\varepsilon} .
$$

Moreover, for every $\tau \ge 0$, $T^* \le \tau + T_1(\Phi^0_\tau(S_0,I_0))$, where $T_1$ is the eradication time under full vaccination $u \equiv 1$ and $\Phi^0$ the uncontrolled flow; in particular $T^* \le T_1(S_0, I_0)$.

## Expansion

Under $u \equiv 1$ the susceptible fraction decays at least like $S_0 e^{-t}$, so after time $t_c$ one has $\beta S \le \gamma_{\min}/2$ and $\dot I \le -\tfrac{\gamma_{\min}}{2} I$; before $t_c$ the growth of $\ln I$ is at most $\beta_{\max} S_0 t_c$ in total. Integrating the bound on $\frac{d}{dt}\ln I$ gives the estimate. In the subcritical regime $\dot I \le -(\gamma_{\min} - \beta_{\max} S_0) I$ from the start. The two-policy bound follows by concatenating the uncontrolled flow with full vaccination, which is admissible.

## Sources

- Yeachan Park, Jiwoong Jang and Yeoneung Kim, *Time-optimal vaccination in state-dependent SIR models: a single switch criterion and numerical examples outside its regime*, arXiv:2610.23095, Theorem 2 and Corollary 1 (Section 4). <https://doi.org/10.48550/arXiv.2610.23095>
