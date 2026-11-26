# Well-posedness and ODE reduction of the age-structured role-reversal model

**Model.** Let $x(t)$ be the prey population and $u(t,\tau)$ the age density of predators, with maturation age $\tau^* > 0$, juveniles $y_1(t) = \int_0^{\tau^*}u(t,\tau)\,d\tau$ and adults $y_2(t) = \int_{\tau^*}^\infty u(t,\tau)\,d\tau$. The system is

$$x' = x(r - ax + sy_1 - by_2), \qquad u_t + u_\tau = -\mu(x,\tau)u, \qquad u(t,0) = \int_0^\infty B(x,\tau)u(t,\tau)\,d\tau,$$

with $x(0) = x_0$, $u(0,\tau) = u_0(\tau)$ and

$$B(x,\tau) = kx\,\varphi_{\{\tau \ge \tau^*\}}(\tau) + \tilde B(\tau)(1 - e^{-\zeta x}), \qquad \mu(x,\tau) = gx\,\varphi_{\{\tau < \tau^*\}}(\tau) + \mu_B(\tau) + \mu_M e^{-\rho x},$$

where $\varphi$ are logistic smoothings of the indicators of $[\tau^*,\infty)$ and $(-\infty,\tau^*)$ and $\tilde B$ vanishes on $[0,\tau^*)$. Prey benefit from eating juvenile predators (term $sy_1$, juvenile death $gx$) and are eaten by adults (term $by_2$, predator births $kx$); predators also reproduce at a base rate and die of age ($\mu_B$) and hunger ($\mu_M e^{-\rho x}$).

**Theorem (local well-posedness).** Let $x_0 > 0$, let $u_0 \ge 0$ be piecewise smooth with compact support in $[0,\tau_{0,\max}]$, let $r, a, s, b, \mu_M > 0$ and $k, g \ge 0$, let $\tilde B$ be continuous, positive and bounded and $\mu_B$ continuous, positive and bounded on bounded age intervals. Then for every $T > 0$ there is $T^* \in (0, T]$ such that on $[0, T^*]$ the solution exists, is unique and is positive. The paper's numerical scheme with equal time and age step $h$ converges to it, with error in the age density of order $O(h)$ in the norm $\|(x,u)\| = |x| + \int_0^{\tau_{\max}(t)}|u|\,d\tau$.

**ODE reduction.** Integrating the transport equation over $[0,\tau^*)$ and $[\tau^*,\infty)$, using sharp indicators, the equilibrium maturation rate $D = \bar u(\tau^*)/y_1$ and age-averaged rates $b_2, m_1, m_2$ gives

$$y_1' = kxy_2 + (1 - e^{-\zeta x})b_2y_2 - gxy_1 - m_1y_1 - \mu_Me^{-\rho x}y_1 - Dy_1, \qquad y_2' = Dy_1 - m_2y_2 - \mu_Me^{-\rho x}y_2,$$

which reduces to the role-reversal ODE of Li, Liu and Wei when the base birth term and the hunger deaths are removed.

## Expansion

The predator age density is transported along characteristics with an $x$-dependent death rate, so it stays compactly supported at finite times; existence is proved by showing that the numerical solutions are locally Lipschitz in the $L^1$-type norm, stay in a ball for a time independent of $h$, and converge; uniqueness is proved separately in the same norm. Positivity of $x$ comes from its logistic form, and positivity of $u$ in the trapezoid $\{0 \le \tau < \tau_{0,\max} + t\}$ from the characteristic representation. Replacing the maturation flux $u(t,\tau^*)$ by integration along the characteristic of the generation born at $t - \tau^*$ instead yields a delay differential equation, which keeps the delay between birth and maturation that the ODE loses.

## Sources

- L. Suarez, M. K. Cameron, W. F. Fagan and D. Levy, "A predator-prey model with age-structured role reversal", arXiv preprint (2025), Sections 2, 4 and 5, Theorem 1 and Lemmas 1 to 8. <https://doi.org/10.48550/arXiv.2502.19748>