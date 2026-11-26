# Redundancy of the treatment sign constraint in SIRS treatment–vaccination control

**Model.** Let $N$ be the total population, $S$ the susceptibles and $I$ the infecteds, with recovered $R = N - S - I$. With logistic recruitment $F(N) = \alpha N (1 - N/K)$, natural death rate $\mu$, disease death rate $\delta$, incidence rate $\beta$, recovery rate $\gamma$ and waning rate $\omega$, the controlled SIRS dynamics are

$$\dot N = F(N) - \delta I - \mu N, \qquad \dot S = F(N) - \beta \frac{IS}{N} - vS + \omega (N - S - I) - \mu S, \qquad \dot I = \beta \frac{IS}{N} - (\gamma + \delta + u) I - \mu I,$$

where $v(t) \in [0, v_{\max}]$ is the vaccination rate (moving susceptibles to $R$) and $u(t)$ the treatment rate (moving infecteds to $R$). On a horizon $[0,T]$ with fixed initial data, minimize

$$C(T) = \int_0^T \bigl( B_1 I(s) + B_2 v(s) + B_3 u(s)^2 \bigr)\, ds, \qquad B_1, B_2, B_3 > 0.$$

**Proposition.** If $(\hat u, \hat v)$ is optimal for this problem with the constraints $0 \le v \le v_{\max}$ and $u \ge 0$, then $\hat u \ge 0$ a.e.; more precisely, replacing any treatment $u$ by $\max\{u, 0\}$ (with $v$ unchanged) never increases the infected trajectory or the cost. Hence the sign constraint on the treatment is redundant and may be dropped: the problem becomes one with an unconstrained nonlinear (quadratic-cost) control $u$ and a box-constrained affine control $v$.

**Structure of the vaccination control.** Because $v$ enters linearly, along an optimal path $v$ is a concatenation of bang arcs ($v \in \{0, v_{\max}\}$) and singular arcs, on which the switching function $H_v$ vanishes identically; writing the dynamics as $\dot x = f_0(x,u) + v f_1(x)$ for $x = (N, S, I, C)$ with $f_1 = (0, -S, 0, B_2)^{\mathsf T}$, the singular vaccination rate is obtained from the second time derivative of $H_v$, as the feedback $v_{\mathrm{sing}} = -\gamma_{01}/\gamma_{11}$ in terms of Lie-bracket coefficients built from $f_0$, $f_1$ and the costate.

## Expansion

Let $(N,S,I)$ and $(\tilde N, \tilde S, \tilde I)$ be the trajectories under $u$ and $\tilde u = \max\{u,0\}$. The difference $z = \tilde I - I$ satisfies a linear differential inequality $\dot z \le a(t) z + b(t)$ with $b = u I \chi_{\{u<0\}} \le 0$ and $z(0) = 0$, so Grönwall's lemma gives $z \le 0$: removing negative treatment lowers infections, while the quadratic treatment cost and the vaccination cost do not increase. Dropping the constraint is what makes the problem fit a shooting method for partially control-affine problems, where nonlinear controls are eliminated through stationarity of the Hamiltonian and singular affine controls through Goh-type conditions, with the parameters chosen to favor singular vaccination arcs.

## Sources

- M. S. Aronna, J. M. Machado, "The shooting algorithm for partially control-affine problems with application to an SIRS epidemiological model", arXiv (2021). Section 8 (subsection "Optimal Control of an SIRS Epidemiological Model", proposition on non-negative treatment) and Appendix A (computation of singular vaccination strategies). <https://doi.org/10.48550/arXiv.2103.06339>
