# Anytime regret bound for UCB1

Let $K > 1$ and consider $K$ arms whose rewards are independent and identically distributed over time for each arm, independent across arms, and supported in $[0,1]$, with means
$\mu_1, \dots, \mu_K$, $\mu^* = \max_j \mu_j$ and gaps $\Delta_j = \mu^* - \mu_j$. The policy UCB1 plays each
arm once and then, at each step, plays an arm $j$ maximizing $\bar{x}_j + \sqrt{2 \ln n / n_j}$, where
$\bar{x}_j$ is the empirical mean of arm $j$, $n_j$ the number of times it has been played and $n$ the
total number of plays so far. After any number $n$ of plays, its expected regret is at most

$$8 \sum_{i : \mu_i < \mu^*} \frac{\ln n}{\Delta_i} + \Big(1 + \frac{\pi^2}{3}\Big) \sum_{j=1}^K \Delta_j.$$

## Proof depends on

- [Equality in law of the reward-stack and canonical bandit models](equality-in-law-of-the-reward-stack-and-canonical-bandit-models.md)
- [Regret decomposition for stochastic bandits](regret-decomposition-for-stochastic-bandits.md)

## Sources

- P. Auer, N. Cesa-Bianchi and P. Fischer, *Finite-time analysis of the multiarmed bandit problem*, Machine Learning 47 (2002) 235–256, Theorem 1 and Figure 1. <https://homes.di.unimi.it/~cesa-bianchi/Pubblicazioni/ml-02.pdf>
