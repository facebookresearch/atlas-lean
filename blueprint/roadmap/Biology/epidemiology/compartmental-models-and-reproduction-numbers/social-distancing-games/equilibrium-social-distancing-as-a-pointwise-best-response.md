# Equilibrium social distancing as a pointwise best response

**Epidemic.** A closed population of size $N$ follows SIR dynamics in which the transmission rate is scaled by the relative risk of the population's aggregate distancing investment $\bar\kappa(t) \ge 0$ per day:

$$S' = -b\, \beta(\bar\kappa) \frac{S I}{N}, \qquad I' = b\, \beta(\bar\kappa) \frac{S I}{N} - g I, \qquad R' = g I,$$

with baseline transmission rate $b > 0$ and removal rate $g > 0$. The **relative risk** $\beta \colon [0, \infty) \to (0, 1]$ satisfies $\beta(0) = 1$, is decreasing, bounded below by $0$ and, by diminishing returns, convex.

**Individual.** One susceptible individual using investment $\kappa(t)$ is infected at hazard $b\, \beta(\kappa(t))\, I(t)/N$; in an infinite population this choice does not affect $I(t)$. Infection costs $c_I > 0$ per day of illness, distancing costs $\kappa$ per day. Let $V_S(t)$ and $V_I(t)$ be the expected present values (negative expected future costs) of being susceptible or infected at time $t$ under the individual's strategy, so $V_S - V_I > 0$ is the expected cost averted by staying uninfected. In the absence of discounting, the values obey the adjoint (Bellman) equations of the individual's three-state Markov decision process,

$$-V_S' = -\kappa + b\, \beta(\kappa) \frac{I}{N} (V_I - V_S), \qquad -V_I' = -c_I + g (V_R - V_I),$$

with $V_R$ the (constant) value of the removed state.

**Proposition (pointwise best response, necessary condition).** If a strategy maximizes $V_S$ against a given epidemic course, then at almost every time it minimizes the instantaneous expected loss

$$\kappa + b\, \beta(\kappa) \frac{I(t)}{N} \big(V_S(t) - V_I(t)\big)$$

over $\kappa \ge 0$ (the maximum principle, Eq. (13) of the source). If $\beta$ is differentiable and strictly convex, the minimizer is unique: writing $\Delta(t) = b\, (I(t)/N)\, (V_S(t) - V_I(t)) \ge 0$,

$$\kappa^*(t) = 0 \ \text{ if } -\beta'(0)\, \Delta(t) \le 1, \qquad \text{otherwise } \kappa^*(t) \text{ solves } -\beta'(\kappa^*)\, \Delta(t) = 1 .$$

A **Nash equilibrium** is a feedback strategy $\kappa^*$ that is a best response to itself: the epidemic is driven by $\bar\kappa = \kappa^*$ and every individual's best response to that epidemic is again $\kappa^*$; it is subgame perfect if this holds from every state the system can pass through.

Properties:

- the equilibrium investment is zero whenever prevalence $I/N$ or the value at stake $V_S - V_I$ is small, and increases with both, since $-\beta'$ is decreasing in $\kappa$;
- the equilibrium internalizes only the individual's own risk, not the externality of reduced onward transmission, so it differs from the community-optimal policy.

## Depends on

- [Solution of the Kermack–McKendrick SIR system](../../kermack-mckendrick-sir-model/is-solution.md)

## Expansion

The value of the susceptible state changes at rate equal to the flow cost of distancing plus the hazard of infection times the jump in value $V_I - V_S$; choosing $\kappa$ to make this rate as favourable as possible at each instant is the maximum principle for the individual's control problem; the source states it as a necessary condition satisfied by every subgame perfect equilibrium, and the page claims no converse. The greedy (Isaacs) construction of the equilibrium applies it with the population strategy fed back into the epidemic. For a convex differentiable decreasing $\beta$, the function $\kappa \mapsto \kappa + \beta(\kappa)\Delta$ is convex with derivative $1 + \beta'(\kappa)\Delta$; it is minimized at $0$ if that derivative is non-negative at $0$, and otherwise at its unique zero, since strict convexity makes $\beta'$ strictly increasing. Existence and uniqueness of subgame perfect equilibria (finite-time blow-up of the associated Hamilton–Jacobi equation) are not proved, but numerical and analytical evidence supports uniqueness.


In numerical computations for the specific working choice $\sigma(c) = 1/(1+mc)$ with $m = 10$ (Reluga 2010, Eq. (6) and Figure 1), Reluga observes that in the infinite-horizon problem without vaccination, equilibrium investment in social distancing decreases with the susceptible fraction and is largest when the susceptible fraction is smallest; this is a numerical finding for that choice of $\sigma$ rather than a general theorem for the class above.

## Sources

- T. C. Reluga, "Game theory of social distancing in response to an epidemic", PLoS Computational Biology 6 (2010), e1000793, sections "The Social Distancing Game" and "Game Analysis", <https://doi.org/10.1371/journal.pcbi.1000793> (PMC2877723).
