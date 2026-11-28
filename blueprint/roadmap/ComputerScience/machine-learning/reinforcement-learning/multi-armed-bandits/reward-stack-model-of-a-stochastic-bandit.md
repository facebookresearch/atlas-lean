# Reward-stack model of a stochastic bandit

Let $\nu = (P_1, \dots, P_k)$ be a stochastic bandit and $\pi$ a policy, and fix a horizon $n$. The reward-stack
model takes mutually independent random variables $X_{s,i} \sim P_i$ for $s \le n$ and $i \le k$, independent of
the policy's internal randomization. At round $t$ the arm $A_t$ is drawn from the policy's kernel applied to the
realized history, and the observed reward is $X_t = X_{T_{A_t}(t),\,A_t}$, the next unused entry of the chosen arm's
stack, where $T_i(t)$ is the number of times arm $i$ has been chosen in rounds $1, \dots, t$.

## Depends on

- [Stochastic k-armed bandits: canonical history law](stochastic-k-armed-bandits-canonical-history-law-and-regret.md)
- [Pull count of an arm](canonical-bandit-model/pull-count.md)

## Related topics

- [Equality in law of the reward-stack and canonical bandit models](equality-in-law-of-the-reward-stack-and-canonical-bandit-models.md): the law of the interaction $(A_1, X_1, \dots, A_n, X_n)$ in the reward-stack model is the canonical law.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), §4.6 (the reward-stack model) and Exercise 4.4. <https://tor-lattimore.com/downloads/book/book.pdf>
