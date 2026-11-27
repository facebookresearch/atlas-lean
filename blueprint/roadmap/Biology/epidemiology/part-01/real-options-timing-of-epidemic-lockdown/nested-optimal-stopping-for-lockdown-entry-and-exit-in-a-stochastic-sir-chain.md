# Nested optimal stopping for lockdown entry and exit in a stochastic SIR chain

**Chain.** A population of $N$ individuals has $I_t$ infected and $R_t$ removed members, $S_t = N - I_t - R_t$, and state $X_t = (I_t, R_t) \in E = \{(i,r) \in \mathbb{N}^2 : i + r \le N\}$. In policy mode $m \in \{0,1\}$ (no lockdown, lockdown) the generator $Q^m = (q^m_{xy})$ has

$$q^m_{xy} = \begin{cases} \lambda_m(x) = \beta_m\, i\, S(x)/N, & y - x = (1,0),\\ \mu_m(x) = \gamma_m\, i, & y - x = (-1,1),\\ 0, & \text{otherwise}, \end{cases}\qquad q^m_{xx} = -\sum_{y \ne x} q^m_{xy},$$

and the absorbing set is $\Lambda = \{(i,r) \in E : i = 0\}$. Running costs are $c_m(i,r) = \delta_E(i,r)\, i + \delta_L\, \mathbf{1}\{m=1\}$ with $\delta_E(0,r) = 0$ and $\delta_L > 0$; switching from mode $m$ to $m'$ costs $K_{mm'} \ge 0$; costs are discounted at rate $\rho > 0$.

**Value after lockdown (Proposition 1).** $G(x) = \mathbb{E}^0_x\big[\int_0^\infty e^{-\rho t} c_0(X_t)\,dt\big]$ satisfies

$$G(x) = \frac{c_0(x)}{\rho - q^0_{xx}} + \sum_{y \ne x} \frac{q^0_{xy}}{\rho - q^0_{xx}}\, G(y),\qquad G(x) = \frac{c_0(x)}{\rho}\ \ (x \in \Lambda).$$

**Value in lockdown (Proposition 2).** The exit problem $F(x) = \inf_\tau \mathbb{E}^1_x\big[e^{-\rho\tau}(G(X_\tau) + K_{10}) + \int_0^\tau e^{-\rho t} c_1(X_t)\,dt\big]$ has $F = \varphi$, where $\varphi : E \to \mathbb{R}_+$ is the unique solution of

$$\varphi(x) = \min\Big\{ G(x) + K_{10},\ \frac{c_1(x)}{\rho - q^1_{xx}} + \sum_{y \ne x} \frac{q^1_{xy}}{\rho - q^1_{xx}}\, \varphi(y) \Big\},$$

and the optimal exit time is the first exit time from $C_1 = \{x : \varphi(x) < G(x) + K_{10}\}$.

**Value before lockdown (Proposition 3).** The entry problem $V(x) = \inf_\tau \mathbb{E}^0_x\big[e^{-\rho\tau}(F(X_\tau) + K_{01}) + \int_0^\tau e^{-\rho t} c_0(X_t)\,dt\big]$ has $V = \psi$, the unique solution of

$$\psi(x) = \min\Big\{ F(x) + K_{01},\ \frac{c_0(x)}{\rho - q^0_{xx}} + \sum_{y \ne x} \frac{q^0_{xy}}{\rho - q^0_{xx}}\, \psi(y) \Big\},$$

and lockdown is optimally imposed at the first exit time from $C_0 = \{x : \psi(x) < F(x) + K_{01}\}$. Together these solve the nested problem of choosing $\tau_1 \le \tau_2$ (entry and exit times) to minimize total expected discounted cost.

## Depends on

- [Kermack–McKendrick SIR model](../../kermack-mckendrick-sir-model/README.md)

## Expansion

From state $x$ the chain waits an exponential time with rate $-q_{xx}$, accruing cost at rate $c(x)$, and then jumps to $y$ with probability $q_{xy}/(-q_{xx})$. Discounting the holding time gives the factor $1/(\rho - q_{xx})$ in front of both the running cost and the continuation values, which is Proposition 1 (equivalently the Bellman equation $\rho G = Q^0 G + c_0$). For the stopping problems, the planner compares at each state the cost of switching now with the cost of waiting one transition; the quasi-variational inequality $\min\{G + K_{10} - \varphi,\ (Q^1 - \rho)\varphi + c_1\} = 0$ has a unique bounded solution because the one-step operator is a contraction with modulus $\max_x (-q_{xx})/(\rho - q_{xx}) < 1$ on the finite state space. Numerically, with SARS-CoV-2-like parameters the stopping regions imply early lockdown and exit only well after the peak of infections.

## Sources

- N. F. D. Huberts, J. J. J. Thijssen, "Optimal timing of non-pharmaceutical interventions during an epidemic", European Journal of Operational Research 305(3) (2023) 1366–1389, Section 2 (Eqs. (1)–(3)), Section 3 (Eqs. (4)–(10), Propositions 1–3) and Appendix A, <https://doi.org/10.1016/j.ejor.2022.06.034>, PMCID PMC9221090.
