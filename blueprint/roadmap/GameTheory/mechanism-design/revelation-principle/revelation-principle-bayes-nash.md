# Revelation principle (Bayesian, pure strategies)

Let $I$ be a finite set of agents with finite type sets $\Theta_i$, action sets $X_i$ and an outcome set $O$, and let $p$ be a prior on type profiles, a probability distribution on the finite set $\prod_j \Theta_j$ ($p \ge 0$, $\sum_\theta p(\theta) = 1$). Utilities $u_i(\theta, o) \in \mathbb{R}$ may depend on the whole type profile $\theta$, and $U_i(\theta_i, h)$ is the interim expected utility of agent $i$ of type $\theta_i$ when each profile $\theta$ leads to the outcome $h(\theta)$.
If the pure strategies $s$ form a Bayesian Nash equilibrium of the mechanism $g$, then the direct mechanism
$\theta \mapsto g\bigl((s_j(\theta_j))_j\bigr)$ is Bayesian incentive compatible, and by construction its
truthful outcome at every type profile is the equilibrium outcome of $g$, so every type of every agent gets
the same interim utility (Myerson 1979, Theorem 2; Myerson 1981, Lemma 1). Myerson's Theorem 2 also allows
randomized response plans (mixed strategies); this statement covers pure strategies only, with an arbitrary
outcome set $O$, which may itself be a set of lotteries.

## Background

- [Bayesian Nash equilibrium](is-bayes-nash.md): the hypothesis, applied to the deviation to the action prescribed for the reported type.
- [Bayesian incentive compatibility](is-bayes-incentive-compatible.md): the conclusion.

## Sources

- R. B. Myerson, "Incentive compatibility and the bargaining problem", *Econometrica* 47(1) (1979), 61–73, §3, Theorem 2 (with randomized response plans).
- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, Lemma 1.
- R. B. Myerson and M. A. Satterthwaite, "Efficient mechanisms for bilateral trading", *Journal of Economic Theory* 29 (1983), 265–281, §2.
