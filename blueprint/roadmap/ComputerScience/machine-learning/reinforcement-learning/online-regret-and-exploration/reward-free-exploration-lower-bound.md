# Lower bound for reward-free exploration

Any reward-free exploration algorithm that returns $\varepsilon$-optimal policies for all reward functions with probability at least $1/2$ needs $\Omega(S^2AH^2/\varepsilon^2)$ exploration episodes in expectation on some episodic MDP, even when its policies may be randomized and history-dependent and even when transitions and rewards do not depend on the stage.

There is a universal constant $C > 0$ such that the following holds. Let $A \ge 2$, $S \ge C\log_2 A$, $H \ge C\log_2 S$ and $0 < \varepsilon \le \min\{1/4, H/48\}$. Every algorithm for [reward-free exploration](reward-free-exploration.md) that meets its success criterion with failure probability $p = 1/2$ and accuracy $\varepsilon$, that is, returns $\varepsilon$-optimal policies for an arbitrary number of reward functions with values in $[0, 1]$, collects, on some MDP depending on the algorithm and on $\varepsilon$, in expectation

$$
\Omega\Big(\frac{S^2 A H^2}{\varepsilon^2}\Big)
$$

exploration episodes, the MDP being an [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) with $S$ states, $A$ actions and horizon $H$. This remains true if the algorithm may return randomized or history-dependent policies, and if the rewards and transitions of the MDPs considered are identical across stages.

## Depends on

- [Reward-free exploration](reward-free-exploration.md)
- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)

## Proof depends on

- [Fano's method: lower bound on the error of multiple hypothesis testing](../../../../Probability/statistical-estimation/minimax-lower-bounds/fano-and-two-point-minimax-rates/fano-multiple-testing-lower-bound.md)
- [Two-sided Hoeffding inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-abs-avg-sub-ge-le.md)

## Expansion

The bound matches the $S^2A/\varepsilon^2$ dependence of the [reward-free upper bound](reward-free-exploration-upper-bound.md), up to logarithmic factors and lower-order terms, and leaves a gap of $H^3$. Its factor $S^2$, instead of the factor $S$ of a single known reward, comes from having to learn whole next-state distributions: in the core instance only the transitions out of one state are unknown, and the factor $S$ arises because they go to $\Theta(S)$ states. The bound holds against an unlimited number of reward functions; whether it holds when only a few reward functions, fixed in advance, must be optimized is left open by the authors.

The core instance has a single initial state $0$ and $2n$ absorbing states, with transition probabilities $q(s, a)$ from $0$ to $s$ under action $a$ within $\varepsilon/(2n)$ of uniform, and state-dependent, action-independent rewards $\nu(s) \in [0, 1]$ on the absorbing states. Being correct for exponentially many reward vectors $r_\nu$ lets one decode, for each action, a member of a packing of $\exp(\Omega(n))$ transition vectors, and the center form of Fano's inequality, average error at least $1 - (\log 2 + \frac1M\sum_j \mathrm{KL}(P_j, P_0))/\log M$ for any comparison law $P_0$, then forces $\Omega(nA/\varepsilon^2)$ episodes when $n \ge c_0\log_2 A$ (Lemma 4.2). The packing exists by the probabilistic method: for random balanced sign vectors, the two-sided Hoeffding bound for the average of $n$ fair coin flips, $\Pr[|W/n - 1/2| \ge \gamma/2] \le 2e^{-2(\gamma/2)^2 n}$, applied after comparing the count of agreements with a binomial one, and a union bound over pairs make all inner products small.

Two proof steps have no exact page. The Kullback–Leibler divergence between the laws of the exploration data under two instances is written, by a Wald-identity argument, as the expected number of plays of the affected action times a one-step divergence; the [divergence decomposition for stochastic bandits](../multi-armed-bandits/divergence-decomposition-for-stochastic-bandits.md) is the bandit analogue with a fixed horizon, not this statement with a random number of episodes. And the Fano page is stated for observations in a finite set, while the exploration data, with a random number of episodes, take countably many values. Both are missing proof prerequisites. A good expansion also gives pages to the steps of the appendix of arXiv:2002.02794v1: the formal single-instance Lemma D.2, Lemma D.3 (a near-optimal policy reaches the chosen instance with probability at least $1/2$), the embedding correspondence Lemma D.4, the packing Lemma D.6 with its concentration Lemma D.9, the estimation bound Lemma D.7 from the Fano variant Lemma D.10, the reduction of estimation to exploration Lemma D.8 with Lemma D.11, and the proof of Theorem 4.1 in Section D.3. Embedding $n = \Omega(S)$ such instances as the second-to-last layer of a binary tree of depth $1 + \log_2 n$, which the learner steers through deterministically, and adding reward $1$ at one chosen instance forces any near-optimal policy to go there and act near-optimally, so the learner must solve all $n$ instances: $\Omega(n \cdot nA/\varepsilon^2) = \Omega(S^2A/\varepsilon^2)$. Using the absorbing leaves to collect a chain of $\Omega(H)$ rewards improves this to $\Omega(S^2AH^2/\varepsilon^2)$.

## Sources

- C. Jin, A. Krishnamurthy, M. Simchowitz and T. Yu, "Reward-Free Exploration for Reinforcement Learning", *Proceedings of the 37th International Conference on Machine Learning* (ICML 2020), PMLR 119: Theorem 4.1 and the remarks after it, Lemma 4.2 and its proof sketch, the embedding into a binary tree in Section 4, and the appendix proof of the lower bound (the single-state lemma, the embedding correspondence and Fano's inequality). [PDF](https://proceedings.mlr.press/v119/jin20d/jin20d.pdf)
