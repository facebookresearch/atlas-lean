# UCRL2 and extended value iteration

UCRL2 is an optimistic algorithm for learning in an unknown communicating MDP. It proceeds in episodes; at the start of each it forms confidence sets around the empirical rewards and transition laws, uses extended value iteration to pick a plausible MDP and a policy with nearly the highest optimal average reward, and follows that policy until some state-action count doubles.

Let $M$ be an unknown finite MDP with $S$ states, $A$ actions, rewards in $[0, 1]$ with means $\bar r(s, a)$, and transition laws $p(\cdot \mid s, a)$; only $\mathcal{S}$, $\mathcal{A}$ and a confidence parameter $\delta \in (0, 1)$ are given. At time $t_k$, the start of episode $k$, UCRL2 forms the counts $N_k(s, a)$ of earlier visits, the empirical means $\hat r_k(s, a)$ and empirical transition laws $\hat p_k(\cdot \mid s, a)$, each normalized by $\max\{1, N_k(s, a)\}$, and the set $\mathcal{M}_k$ of MDPs on $\mathcal{S}, \mathcal{A}$ with rewards $\tilde r(s, a) \in [0, 1]$ and transition laws $\tilde p(\cdot \mid s, a)$ such that

$$
|\tilde r(s, a) - \hat r_k(s, a)| \le \sqrt{\frac{7\log(2SAt_k/\delta)}{2\max\{1, N_k(s, a)\}}}, \qquad \big\lVert \tilde p(\cdot \mid s, a) - \hat p_k(\cdot \mid s, a)\big\rVert_1 \le \sqrt{\frac{14S\log(2At_k/\delta)}{\max\{1, N_k(s, a)\}}}.
$$

It then computes, by extended value iteration, an MDP $\tilde M_k \in \mathcal{M}_k$ and a stationary policy $\tilde\pi_k$ with $\min_s \rho(\tilde M_k, \tilde\pi_k, s) \ge \max_{M' \in \mathcal{M}_k, \pi, s'} \rho(M', \pi, s') - 1/\sqrt{t_k}$, where $\rho$ is the average reward. It plays $\tilde\pi_k$ while the number $v_k(s_t, \tilde\pi_k(s_t))$ of visits in the current episode to the current state-action pair is below $\max\{1, N_k(s_t, \tilde\pi_k(s_t))\}$, and starts episode $k+1$ as soon as it is not.

Extended value iteration treats $\mathcal{M}_k$ as one MDP whose actions are the pairs (action, plausible transition law). With $u_0 \equiv 0$ it iterates

$$
u_{i+1}(s) = \max_{a \in \mathcal{A}} \Big\{\tilde r(s, a) + \max_{q \in \mathcal{P}(s, a)} \sum_{s'} q(s')\, u_i(s')\Big\},
$$

where $\tilde r(s, a)$ is the largest plausible reward and $\mathcal{P}(s, a)$ the $\ell_1$ ball of plausible transition laws; the inner maximum moves as much probability as allowed to the state with the largest $u_i$ and removes it from the states with the smallest $u_i$, in $O(S)$ steps after sorting. It stops when $\max_s (u_{i+1}(s) - u_i(s)) - \min_s (u_{i+1}(s) - u_i(s)) < \varepsilon$, here $\varepsilon = 1/\sqrt{t_k}$, and returns the greedy policy for $u_i$ with the maximizing transition laws.

## Depends on

- [Regret against the optimal average reward](regret-against-optimal-average-reward.md)
- [Diameter of a Markov decision process](diameter-of-an-mdp.md)

## Proof depends on

None.

## Expansion

Jaksch, Ortner and Auer prove that if a set of MDPs of this form, with confidence radii $d(s, a) > 0$ for the transitions and $d'(s, a) \ge 0$ for the rewards around given estimates, contains at least one communicating MDP, then extended value iteration converges, and at the stopping rule above the greedy policy is $\varepsilon$-optimal for the combined MDP (their Theorem 7). The point is that the chosen policies are aperiodic, because the inner maximum always puts positive probability on one fixed best state. In UCRL2 the true MDP plays the role of that communicating member with high probability.

The doubling rule means that each episode at most doubles the count of some state-action pair, so the number of episodes up to step $T \ge SA$ is at most $SA\log_2(8T/(SA))$ (their Proposition 18), and the policy is recomputed only that often. The transition confidence set is an $\ell_1$ ball of radius of order $\sqrt{S/N}$, from the deviation inequality for empirical distributions of Weissman and coauthors. UCRL2 is a variant of the UCRL algorithm of Auer and Ortner.

## Sources

- T. Jaksch, R. Ortner and P. Auer, "Near-optimal Regret Bounds for Reinforcement Learning", *Journal of Machine Learning Research* 11 (2010), 1563–1600: Section 3 with Figure 1 (UCRL2 and the confidence sets (3) and (4)), Section 3.1 with Figure 2 (extended value iteration (5) and the inner maximum), Theorem 7 and Remark 8, Appendix C.1 (Lemma 17, which uses the inequality of Weissman, Ordentlich, Seroussi, Verdú and Weinberger) and Appendix C.2 (Proposition 18). [PDF](https://www.jmlr.org/papers/volume11/jaksch10a/jaksch10a.pdf)
