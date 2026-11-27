# Finite-horizon value of a policy

Let $M$ be a Markov decision process with finitely many states $s$, rewards $r(s,a)$ and real transition weights $P(s,a,s')$, let $\gamma \in \mathbb{R}$, and let $\pi$ be a nonstationary policy, where $\pi_k(s)$ is the action taken with $k$ steps remaining in state $s$; the set of actions may be infinite. The finite-horizon value of $\pi$ is defined by $V_0(s) = 0$ and

$$V_{k+1}(s) = r(s, \pi_{k+1}(s)) + \gamma \sum_{s'} P(s, \pi_{k+1}(s), s')\, V_k(s').$$

This is a weighted discounted return. When $M$ is stochastic ($P(s,a,s') \ge 0$ and $\sum_{s'} P(s,a,s') = 1$ for all $s, a$), $V_k(s)$ is the expected discounted return of $\pi$ over $k$ steps from $s$.
