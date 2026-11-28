# Bang-bang threshold best responses in social distancing games

**Model.** Players form a continuum indexed by $i \in [0,1)$ with Lebesgue measure $\mu$. Player $i$'s probabilities of being susceptible, infected, removed or dead evolve as

$$\dot S_i = -r u_i S_i I_f, \quad \dot I_i = r u_i S_i I_f - \alpha_i I_i, \quad \dot R_i = \bar\alpha_i I_i, \quad \dot D_i = (\alpha_i - \bar\alpha_i) I_i,$$

where $u_i(t) \in [u_m, u_M] \subseteq [0,1]$ is $i$'s socialization (time spent in public places) and $I_f(t) = \int I_i(t) u_i(t)\,\mu(di)$ is the density of infected people in public places. With mean action $\tilde u = \int u_i\,\mu(di)$ and $\bar u = \kappa + \tilde u$, player $i$ minimizes over a horizon $T$

$$J_i = G_i\bigl(1 - S_i(T)\bigr) - s_i \int_0^T u_i \bar u\,dt = G_i\Bigl(1 - S_i(0)\,e^{-r\int_0^T u_i I_f\,dt}\Bigr) - s_i\int_0^T u_i \bar u\,dt,$$

with vulnerability $G_i > 0$ and sociability $s_i > 0$. Players know only $S_i, I_i$ and the aggregates $\bar u, I_f$.

**Assumptions.** Finitely many types (all parameters piecewise constant in $i$); decisions constant on intervals $[t_k, t_{k+1})$, $0 = t_0 < \dots < t_N = T$, with action $u^i_k$; measurable action profiles. Let $\bar u_k = \int_{t_k}^{t_{k+1}} \bar u\,dt$ and $I^f_k = \int_{t_k}^{t_{k+1}} I_f\,dt > 0$. Up to constants, $J_i$ is equivalent to the auxiliary cost

$$\tilde J_i(u^i) = -b_i \exp\Bigl(-r\sum_{k=0}^{N-1} u^i_k I^f_k\Bigr) - \sum_{k=0}^{N-1} u^i_k \bar u_k, \qquad b_i = \frac{S_i(0)\,G_i}{s_i}.$$

**Proposition 1 (structure of the best response).** Given the aggregates:

1. every optimal $u^i$ is bang-bang: $u^i \in \{u_m, u_M\}^N$;
2. minimizing $\tilde J_i$ is equivalent to minimizing $-b_i e^{-A} + f(A)$ over $A$, where $f(A) = \inf\{-\sum_k u_k \bar u_k : \sum_k u_k I^f_k = A/r,\ u \in [u_m,u_M]^N\}$;
3. on $[A_m, A_M] = [r u_m \sum_k I^f_k,\ r u_M \sum_k I^f_k]$, $f$ is continuous, non-increasing, convex and piecewise affine with at most $N$ pieces, and $f = \infty$ outside;
4. there are at most $N+1$ optimal action vectors;
5. there is a threshold $\lambda'$ with $u^i_k = u_m$ whenever $\bar u_k / I^f_k \le \lambda'$ and $u^i_k = u_M$ whenever $\bar u_k / I^f_k > \lambda'$.

Consequently the best response is found by evaluating $\tilde J_i$ at the threshold rules $\lambda' \in \{\bar u_k / I^f_k\} \cup \{0\}$ and keeping the minimum (Corollary 1).

**Proposition 2 (monotone comparative statics).** If $b_{i_1} < b_{i_2}$ then the optimal exposures satisfy $A_1 \ge A_2$ and $u^{i_2}_k \le u^{i_1}_k$ for every $k$; if $b_{i_1} = b_{i_2}$ the two optimal actions are comparable coordinatewise.

## Expansion

The exponent $A = r\sum_k u_k I^f_k$ is the cumulative infection pressure; for fixed $A$ the remaining problem is a linear program whose value $f(A)$ is convex and piecewise affine, while $-b_i e^{-A}$ is concave. Their sum is minimized at a breakpoint of $f$ or an endpoint, and Lagrange analysis of the linear program fills the periods in decreasing order of the benefit-to-risk ratio $\bar u_k / I^f_k$, giving the threshold rule. Larger $b_i$ (more vulnerable, less sociable, or more likely still susceptible) raises the marginal value $b_i e^{-A}$ of lowering exposure and so shifts the optimal $A$ down, so such players socialize less in every period.

## Sources

- I. Kordonis, A.-R. Lagos, G. P. Papavassilopoulos, "Dynamic Games of Social Distancing During an Epidemic: Analysis of Asymmetric Solutions", Dynamic Games and Applications 12 (2022) 214–236, Equations (1)–(10), Assumptions 1–5, Propositions 1–2 and Corollary 1, <https://doi.org/10.1007/s13235-021-00403-1>, PMCID PMC8503885.
