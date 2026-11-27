# Optimal public-health incentive in the imitation-dynamics vaccination model

**Model.** Let $S, I, R$ be the susceptible, infected and recovered fractions of a population facing an outbreak with transmission rate $\beta$ and recovery rate $\gamma$, and let $x \in (0, 1)$ be the fraction of individuals who adopt the vaccinating strategy; susceptibles are vaccinated at per-capita rate $x$. A vaccinator's perceived payoff is $-r_v$ (perceived risk of vaccine morbidity) and a non-vaccinator's is $-r_i m I$ (infection morbidity risk $r_i$ times a sensitivity $m$ to current prevalence). Individuals sample others at rate $k$ and imitate strategies with higher payoff, which gives replicator (imitation) dynamics. A public-health effort $u(t) \in [0, u_{\max}]$ (campaigns, risk communication) raises the payoff of vaccinating by $f(u)$, with $f$ increasing and $f(0) = 0$:

$$\dot S = -\beta S I - xS, \qquad \dot I = \beta S I - \gamma I, \qquad \dot x = k\, x(1-x)\bigl(-r_v + r_i m I + f(u)\bigr),$$

with recovered and vaccinated individuals removed from transmission ($R$ does not feed back).
The planner maximizes

$$J(u) = \int_0^T \bigl[-c_I\, \beta S I - \eta\, u\bigr]\, dt$$

(cost $c_I$ per new infection, cost $\eta$ per unit effort) over measurable $u$ with values in $[0, u_{\max}]$.

**Theorem.** An optimal control $u^*$ exists. Along the optimal trajectory, with adjoint variables $\lambda_S, \lambda_I, \lambda_x$ solving $\dot\lambda_j = -\partial H/\partial j$ for the Hamiltonian

$$H = -c_I\beta S I - \eta u + \lambda_S(-\beta S I - xS) + \lambda_I(\beta S I - \gamma I) + \lambda_x\, k x(1-x)\bigl(-r_v + r_i m I + f(u)\bigr),$$

the interior stationarity condition is

$$f'(u_k^*) = \frac{\eta}{\lambda_x\, k\, x^*(1 - x^*)},$$

and $u^*(t)$ is $u_k^*(t)$ projected onto $[0, u_{\max}]$ wherever $H$ is strictly concave in $u$. Examples: for $f(u) = \xi u^2$, $u_k^* = \eta/\bigl(2\xi\lambda_x k x^*(1-x^*)\bigr)$; for linear $f$ the control is bang–bang; and for linear incentive $f(u) = \xi u$ with quadratic cost $\eta u^2$ in $J$,

$$u^*(t) = \min\Bigl\{u_{\max},\ \max\Bigl\{0,\ \frac{\xi\, \lambda_x(t)\, k\, x^*(t)(1 - x^*(t))}{2\eta}\Bigr\}\Bigr\}.$$

The factor $x(1-x)$ shows that effort is worth most when vaccinating behaviour is most divided ($x$ near $1/2$) and worthless when the population is nearly unanimous, because imitation then has no one to copy or no one left to convert.

## Expansion

The $x$-equation is the two-strategy replicator equation $\dot x = k\,x(1-x)\bigl(\pi(V) - \pi(NV)\bigr)$, with payoff gain $\Delta E = -r_v + r_i m I + f(u)$: individuals switch towards vaccinating when perceived infection risk outweighs perceived vaccine risk, so vaccine uptake responds to prevalence with feedback and free riding near herd immunity. Existence follows from convexity of the integrand in $u$, compactness of the control set and Lipschitz state dynamics. The stationarity condition is $\partial H/\partial u = -\eta + \lambda_x k x(1-x) f'(u) = 0$; the adjoint $\lambda_x$ is the marginal value of an extra vaccinator, so effort is high when an extra vaccinator is valuable and the population is persuadable. If perceived vaccine risk decays with cumulative uptake $V_d$ ($\dot V_d = xS$, payoff $-r_v e^{-\delta V_d}$) and disease deaths raise the vaccinating payoff, uptake becomes self-reinforcing, and the same quadratic-cost formula holds with the enlarged adjoint system. Numerically, optimal effort concentrates at the start and the end of the outbreak rather than at its peak.

## Sources

- A. Deka, B. Pantha, S. Bhattacharyya, "Optimal Management of Public Perceptions During A Flu Outbreak: A Game-Theoretic Perspective", *Bulletin of Mathematical Biology* 82 (2020) 139, Eqs. (2)–(8) and (13), Theorems 1–2, Remark 1. <https://doi.org/10.1007/s11538-020-00817-9> (PMC7563916).
- C. T. Bauch, "Imitation dynamics predict vaccinating behaviour", *Proceedings of the Royal Society B* 272 (2005) 1669–1675. <https://doi.org/10.1098/rspb.2005.3153>.
