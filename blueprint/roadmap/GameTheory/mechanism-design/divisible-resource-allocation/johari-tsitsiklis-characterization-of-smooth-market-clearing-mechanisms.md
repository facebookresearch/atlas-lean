# Johari–Tsitsiklis characterization of smooth market-clearing mechanisms

A *smooth market-clearing mechanism* is a differentiable function $D : (0, \infty) \times [0, \infty) \to [0, \infty)$ such that for every capacity $C > 0$, every number of users $R > 1$ and every nonzero bid vector $\theta \in [0, \infty)^R$ there is a unique price $p_D(\theta) > 0$ with $\sum_r D(p_D(\theta), \theta_r) = C$; user $r$ receives $D(p_D(\theta), \theta_r)$ and pays $p_D(\theta)\,D(p_D(\theta), \theta_r)$, and every user's payoff is $-\infty$ at the zero bid vector. Let $\mathcal D$ be the class of these mechanisms for which, for every admissible utility $U_r$, the price-anticipating payoff $U_r(D(p_D(\theta), \theta_r)) - p_D(\theta)\,D(p_D(\theta), \theta_r)$ is concave in $\theta_r > 0$ when $\theta_{-r} = 0$ and in $\theta_r \ge 0$ otherwise, and for which every demand is available at every price: for all $p > 0$ and $d \ge 0$ some $\theta \ge 0$ has $D(p, \theta) = d$. A nonzero $\theta$ is a *competitive equilibrium* if, at the fixed price $\mu = p_D(\theta)$, each $\theta_r$ maximizes $U_r(D(\mu, \bar\theta_r)) - \mu D(\mu, \bar\theta_r)$ over $\bar\theta_r \ge 0$, and a *Nash equilibrium* if each $\theta_r$ maximizes the price-anticipating payoff given $\theta_{-r}$. Let $\rho(D)$ be the infimum, over $C > 0$, $R > 1$, nonnegative admissible utilities and Nash equilibria, of the aggregate utility at the Nash equilibrium divided by the optimal aggregate utility, with $\rho(D) = -\infty$ if some such instance has no Nash equilibrium. For every $D \in \mathcal D$:

1. a competitive equilibrium exists, and every competitive equilibrium allocation is socially optimal;
2. $D(p, \theta) = \theta / B(p)$ for some concave, strictly increasing, differentiable and invertible $B : (0, \infty) \to (0, \infty)$, so the market-clearing allocation is proportional to the bids;
3. $\rho(D) \le 3/4$, with equality if and only if $D(p, \theta) = \theta / (\varepsilon p)$ for some $\varepsilon > 0$, that is, proportional sharing up to a price scaling.

## Proof sketch

Concavity of the price-anticipating payoff for all admissible utilities forces $D(p, \theta) = \theta / B(p)$, so every mechanism in $\mathcal D$ allocates in proportion to the bids and differs from proportional sharing only in its market-clearing price. Competitive equilibria then reduce to those of the Kelly mechanism, and a worst-case analysis of the Nash conditions, as for the Kelly mechanism, gives $\rho(D) \le 3/4$ with equality only for $B(p) = \varepsilon p$.

## Depends on

- [Kelly's proportional allocation mechanism](kellys-proportional-allocation-mechanism.md)

## Proof depends on

- [Johari–Tsitsiklis 3/4 efficiency of the Kelly mechanism](johari-tsitsiklis-3-4-efficiency-of-the-kelly-mechanism.md)
- [Kelly competitive equilibria exist and are socially optimal](kelly-competitive-equilibria-exist-and-are-socially-optimal.md)

## Sources

- Ramesh Johari, "The Price of Anarchy and the Design of Scalable Resource Allocation Mechanisms", Algorithmic Game Theory, Cambridge University Press, 2007.
- Ramesh Johari and John N. Tsitsiklis, "Efficiency of Scalar-Parameterized Mechanisms", Operations Research, 2009.
