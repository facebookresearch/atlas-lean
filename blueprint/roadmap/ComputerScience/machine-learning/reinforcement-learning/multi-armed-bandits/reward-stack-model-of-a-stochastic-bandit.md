# Reward-stack model of a stochastic bandit

Let $\nu = (P_1, \dots, P_k)$ be a stochastic bandit and $\pi$ a policy, and fix a horizon $n$. The reward-stack
model takes mutually independent random variables $X_{s,i} \sim P_i$ for $s \le n$ and $i \le k$, independent of
the policy's internal randomization. At round $t$ the arm $A_t$ is drawn from the policy's kernel applied to the
realized history, and the observed reward is $X_t = X_{T_{A_t}(t),\,A_t}$, the next unused entry of the chosen arm's
stack, where $T_i(t)$ is the number of times arm $i$ has been chosen in rounds $1, \dots, t$. The resulting law of the
interaction $(A_1, X_1, \dots, A_n, X_n)$ is the same as in the canonical bandit model.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Stochastic k-armed bandits: canonical history law and regret.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy), §4.6 (the reward-stack model) and Exercise 4.4. <https://tor-lattimore.com/downloads/book/book.pdf>
