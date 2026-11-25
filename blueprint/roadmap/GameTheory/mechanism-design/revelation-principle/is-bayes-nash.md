# Bayesian Nash equilibrium

Let $I$ be a finite set of agents with finite type sets $\Theta_i$, action sets $X_i$ and an outcome set $O$, and let $p$ be a prior on type profiles, a probability distribution on the finite set $\prod_j \Theta_j$ ($p \ge 0$, $\sum_\theta p(\theta) = 1$). Utilities $u_i(\theta, o) \in \mathbb{R}$ may depend on the whole type profile $\theta$, and $U_i(\theta_i, h)$ is the interim expected utility of agent $i$ of type $\theta_i$ when each profile $\theta$ leads to the outcome $h(\theta)$.
The pure strategy profile $s$, with $s_i : \Theta_i \to X_i$, is a Bayesian Nash equilibrium of the
mechanism $g : \prod_i X_i \to O$ if no agent of any type gains in interim expectation by a unilateral
deviation to another action, the others following $s$: for every agent $i$, type $\theta_i^0$ and action
$a \in X_i$,

$$U_i\bigl(\theta_i^0, \theta \mapsto g(a, s_{-i}(\theta_{-i}))\bigr) \le U_i\bigl(\theta_i^0, \theta \mapsto g(s(\theta))\bigr),$$

where $s(\theta) = (s_j(\theta_j))_j$ (Myerson 1979, (14), restricted to pure response plans).

## Background

- [Interim expected utility](interim-utility.md): the payoffs compared.
- [Nash's theorem](../../noncooperative-games/nash-s-theorem/README.md): Nash equilibria of complete-information games, of which Bayesian Nash equilibria are the incomplete-information analogue.

## Sources

- R. B. Myerson, "Incentive compatibility and the bargaining problem", *Econometrica* 47(1) (1979), 61–73, §3, (14).
