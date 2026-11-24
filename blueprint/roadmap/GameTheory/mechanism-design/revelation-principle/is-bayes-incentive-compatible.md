# Bayesian incentive compatibility

Let $I$ be a finite set of agents with finite type sets $\Theta_i$, action sets $X_i$ and an outcome set $O$, and let $p$ be a prior on type profiles, a probability distribution on the finite set $\prod_j \Theta_j$ ($p \ge 0$, $\sum_\theta p(\theta) = 1$). Utilities $u_i(\theta, o) \in \mathbb{R}$ may depend on the whole type profile $\theta$, and $U_i(\theta_i, h)$ is the interim expected utility of agent $i$ of type $\theta_i$ when each profile $\theta$ leads to the outcome $h(\theta)$.
The direct mechanism $f : \prod_i \Theta_i \to O$ is Bayesian incentive compatible if truthful reporting is
a Bayesian Nash equilibrium, that is, no agent of any type gains in interim expectation by misreporting
while the others report truthfully: for every agent $i$ and types $\theta_i^0, \theta_i' \in \Theta_i$,
$U_i\bigl(\theta_i^0, \theta \mapsto f(\theta_i', \theta_{-i})\bigr) \le U_i(\theta_i^0, f)$ (Myerson 1979,
(6); Myerson 1981, (3.5); Myerson and Satterthwaite 1983, §2).

## Background

- [Interim expected utility](interim-utility.md): the payoffs compared.

## Sources

- R. B. Myerson, "Incentive compatibility and the bargaining problem", *Econometrica* 47(1) (1979), 61–73, §2, (6).
- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, (3.5).
