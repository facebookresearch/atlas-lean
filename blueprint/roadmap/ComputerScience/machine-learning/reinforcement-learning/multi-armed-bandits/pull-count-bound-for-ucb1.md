# Pull-count bound for UCB1

Consider $K$ arms whose rewards are independent, identically distributed for each arm and supported in $[0,1]$:
the $m$-th play of arm $j$ yields the reward $X_{j,m}$, the rewards $X_{j,m}$ are independent, and those of arm
$j$ have a law $\nu_j$ supported in $[0,1]$, with mean $\mu_j$. Let $\mu^* = \max_j \mu_j$ and
$\Delta_i = \mu^* - \mu_i$. UCB1 plays each arm once, in any order, and then, after $t$ plays, an arm maximizing
$\bar x_j + \sqrt{2 \ln t / n_j}$, where $n_j$ is the number of plays of arm $j$ so far and $\bar x_j$ the mean of
their rewards; ties may be broken in any way. The initial order and the ties may depend on further randomness,
provided that every play is a random variable, that is, a measurable function of the outcome. Let $T_i(n)$ be the
number of plays of arm $i$ among the first $n$ plays. For every arm $i$ with gap $\Delta_i > 0$, which needs
$K \ge 2$, and every $n \ge 1$,

$$\mathbb{E}[T_i(n)] \le \frac{8 \ln n}{\Delta_i^2} + 1 + \frac{\pi^2}{3}.$$

The bound also holds for $n = 0$, where $T_i(0) = 0$, with $\ln 0$ read as $0$. The plays are measurable, for
instance, for [UCB1 with least-index tie-breaking](ucb1/ucb1-arm.md) (`ucb1Arm`), which plays the arms in index
order first and then always the least maximizer, on measurable rewards. Breaking ties toward the least index after
an arbitrary initial order would not by itself make the first plays measurable.

## Related topics

- [Pull-count bound for every run of UCB1](lintegral-count-le.md): the same bound for the lower Lebesgue integral of $T_i(n)$, for runs that need not be measurable.
- [Anytime regret bound for UCB1](anytime-regret-bound-for-ucb1.md)

## Sources

- P. Auer, N. Cesa-Bianchi and P. Fischer, *Finite-time analysis of the multiarmed bandit problem*, Machine Learning 47 (2002) 235–256, Figure 1 and the proof of Theorem 1, which bounds $\mathbb{E}[T_i(n)]$ by $\lceil 8 \ln n / \Delta_i^2 \rceil + \pi^2/3$. <https://homes.di.unimi.it/~cesa-bianchi/Pubblicazioni/ml-02.pdf>
