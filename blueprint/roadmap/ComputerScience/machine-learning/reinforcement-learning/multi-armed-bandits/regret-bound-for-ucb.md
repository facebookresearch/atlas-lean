# Regret bound for UCB

Consider the policy UCB$(\delta)$ with $\delta = 1/n^2$ on a stochastic $k$-armed bandit whose reward distributions are
$1$-subgaussian, with suboptimality gaps $\Delta_i$. For every horizon $n$,

$$R_n \le 3 \sum_{i=1}^k \Delta_i + \sum_{i : \Delta_i > 0} \frac{16 \log n}{\Delta_i}.$$

Here UCB$(\delta)$ is the policy that, at each round $t$, plays an arm maximizing the index
$\mathrm{UCB}_i(t-1,\delta) = \hat\mu_i(t-1) + \sqrt{2\log(1/\delta)/T_i(t-1)}$, which is $+\infty$ when $T_i(t-1) = 0$;
$\hat\mu_i(t-1)$ is the empirical mean of arm $i$ and $T_i(t-1)$ the number of times it was played in the first
$t-1$ rounds.

## Proof depends on

- [Equality in law of the reward-stack and canonical bandit models](equality-in-law-of-the-reward-stack-and-canonical-bandit-models.md)
- [Regret decomposition for stochastic bandits](regret-decomposition-for-stochastic-bandits.md)

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), Algorithm 3, equation (7.2) and Theorem 7.1. <https://tor-lattimore.com/downloads/book/book.pdf>
