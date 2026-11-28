# Thrombin waves of the six-factor monotone coagulation system

**Model.** Let $u = (T, U_5, U_8, U_9, U_{10}, U_{11})$ be the concentrations of thrombin and of activated factors V, VIII, IX, X and XI in plasma, all diffusing with the same coefficient $D > 0$. After quasi-equilibrium reduction of the complexes [Va, Xa] and [VIIIa, IXa] and first-order approximation of activation reactions, the coagulation cascade becomes

$$
\begin{aligned}
\partial_t T &= D\,\Delta T + \Big(k_2 U_{10} + \overline{k_2}\,\frac{k_{510}}{h_{510}}\,U_{10} U_5\Big)\Big(1 - \frac{T}{T_0}\Big) - h_2 T,\\
\partial_t U_5 &= D\,\Delta U_5 + k_5 T - h_5 U_5, \qquad \partial_t U_8 = D\,\Delta U_8 + k_8 T - h_8 U_8,\\
\partial_t U_9 &= D\,\Delta U_9 + k_9 U_{11} - h_9 U_9, \qquad \partial_t U_{11} = D\,\Delta U_{11} + k_{11} T - h_{11} U_{11},\\
\partial_t U_{10} &= D\,\Delta U_{10} + k_{10} U_9 + \overline{k_{10}}\,\frac{k_{89}}{h_{89}}\,U_9 U_8 - h_{10} U_{10},
\end{aligned}
$$

with positive rate constants $k_i, h_i$ and prothrombin level $T_0$. Writing it as $\partial_t u = D\Delta u + F(u)$, the system is **monotone** (quasi-monotone): $\partial F_i / \partial u_j \ge 0$ for all $i \ne j$ in the relevant region $0 \le T \le T_0$.

**Theorem (reduction of equilibria to a quartic).** Equilibria of $u' = F(u)$ are in one-to-one correspondence with the roots $T^* \ge 0$ of the quartic $P(T) = aT^4 + bT^3 + cT^2 + dT$ (explicit coefficients in the rate constants, $a > 0$), via $U_5 = \tfrac{k_5}{h_5}T$, $U_8 = \tfrac{k_8}{h_8}T$, $U_{11} = \tfrac{k_{11}}{h_{11}}T$, $U_9 = \tfrac{k_9 k_{11}}{h_9 h_{11}}T$, $U_{10} = \tfrac{k_9 k_{11}}{h_{10} h_9 h_{11}}\big(k_{10} T + \overline{k_{10}}\tfrac{k_{89}}{h_{89}}\tfrac{k_8}{h_8} T^2\big)$. The source's (7) prints this formula without the factor $k_8/h_8$; the factor follows from the $U_{10}$ equation with $U_8 = \tfrac{k_8}{h_8}T$, and the source's quartic coefficient carries it. The principal eigenvalue of $F'(u^*)$ is positive if and only if $P'(T^*) < 0$, and negative if and only if $P'(T^*) > 0$.

**Theorem (existence of coagulation waves).** Let $P(T^*) = 0$ for some $T^* > 0$ with $P'(0) \ne 0$, $P'(T^*) \ne 0$, and let $u^*$ be the corresponding equilibrium.

- *Monostable case:* if $P$ has no other positive root, then for every $c \ge c_0$ (a minimal speed) there is a monotonically decreasing travelling wave $u(x,t) = w(x - ct)$ with $w(-\infty) = u^*$, $w(+\infty) = 0$.
- *Bistable case:* if $P$ has exactly one more positive root in $(0, T^*)$, there is a monotonically decreasing travelling wave connecting $u^*$ to $0$ for a unique speed $c$.

In the bistable case the wave is globally asymptotically stable; in the monostable case the minimal-speed wave is globally stable and faster waves are stable in weighted norms.

**Theorem (fast-variable reduction).** For the bistable system $u'' + cu' + f(u,v) = 0$, $v'' + cv' + \varepsilon^{-1}(au - bv) = 0$ with $\partial f/\partial v > 0$, the wave speed $c_\varepsilon$ converges as $\varepsilon \to 0$ to the speed $c_0$ of the scalar equation $u'' + cu' + f(u, \tfrac{a}{b}u) = 0$.

## Expansion

At an equilibrium every equation except the thrombin one is linear in its own variable, so all factors can be eliminated in terms of $T$, leaving $P(T) = 0$. For a monotone system the Jacobian $F'(u^*)$ is a Metzler matrix and its principal eigenvalue (Perron-Frobenius) has a positive eigenvector; comparing with the scalar reduced equation $\partial_t T = -P(T)$ shows that its sign is the sign of $-P'(T^*)$. Since $a > 0$, the largest root $T^*$ has $P'(T^*) > 0$ and is stable, while $0$ is unstable when no root lies between and stable when one does. The general theory of travelling waves for monotone parabolic systems (comparison principle, Leray-Schauder degree and minimax speed representations) then yields the monostable half-line of speeds and the unique bistable speed. The speed convergence uses minimax estimates for the speed that are uniform in $\varepsilon$. Biologically the bistable case is the relevant one: a sub-threshold perturbation decays, while a sufficient one triggers a thrombin front whose speed sets the rate of clot growth.

## Proof depends on

- [Perron–Frobenius theorem for irreducible nonnegative matrices](../../../../../LinearAlgebra/special-matrices/perron-frobenius-theorem/perron-frobenius.md)

## Sources

- Tatiana Galochkina, Anass Bouchnita, Polina Kurbatova and Vitaly Volpert, "Reaction-diffusion waves of blood coagulation", arXiv (2016), Section 2.2 (reduced model), Section 3, Theorem 1 (equilibria and principal eigenvalue), Theorem 2 (monostable and bistable waves), Section 4.1, Theorem 3 (speed convergence), <https://doi.org/10.48550/arXiv.1604.07635>.
- A. I. Volpert, V. A. Volpert and V. A. Volpert, *Traveling Wave Solutions of Parabolic Systems*, American Mathematical Society (1994).
