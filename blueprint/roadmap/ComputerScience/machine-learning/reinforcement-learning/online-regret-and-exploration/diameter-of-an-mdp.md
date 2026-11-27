# Diameter of a Markov decision process

The diameter of a finite MDP is the largest, over ordered pairs of distinct states, of the least expected number of steps a stationary deterministic policy needs to move from the first state to the second. An MDP with finite diameter is called communicating.

Let $M$ be a [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md) with a finite set $\mathcal{S}$ of at least two states, finite action set $\mathcal{A}$ and transition probabilities $p(s' \mid s, a)$. For a stationary deterministic policy $\pi : \mathcal{S} \to \mathcal{A}$ and states $s, s'$, let $T(s' \mid M, \pi, s)$ be the first time step at which state $s'$ is reached when $\pi$ is run on $M$ from the initial state $s$, a random variable with values in $\{1, 2, \dots\} \cup \{\infty\}$. The diameter of $M$ is

$$
D(M) = \max_{s \ne s' \in \mathcal{S}}\ \min_{\pi : \mathcal{S} \to \mathcal{A}} \mathbb{E}\big[T(s' \mid M, \pi, s)\big] \in [1, \infty],
$$

with $D(M) = \infty$ when some state cannot be reached almost surely from another under any stationary policy. $M$ is communicating if $D(M) < \infty$.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

None.

## Expansion

The diameter depends only on the transition structure, not on the rewards. It is the time scale on which a learner that has drifted into a poor part of the state space can return to a good part, which is why it enters the [regret bound of UCRL2](ucrl2-regret-bound.md) and the [regret lower bound for MDPs with a given diameter](regret-lower-bound-for-given-diameter.md). In a communicating MDP the optimal long-run average reward does not depend on the initial state. Jaksch, Ortner and Auer also show that the minimal expected times to reach the states of a set $U$, summed over $U$, are at least $\min\sum_k k\,n_k$ over integers $0 \le n_k \le A^k$ with $\sum_k n_k = |U|$; with $U = \mathcal{S}$ this gives $D(M) \ge \log_A S - 3$ for every MDP with $S$ states and $A \ge 2$ actions, so the diameter cannot be small for large state spaces. The diameter can be arbitrarily large, and with $S$ and $A$ fixed it is not always minimized by an MDP with deterministic transitions.

## Sources

- T. Jaksch, R. Ortner and P. Auer, "Near-optimal Regret Bounds for Reinforcement Learning", *Journal of Machine Learning Research* 11 (2010), 1563–1600: Definition 1, the discussion after it in Section 1, and Appendix A (Theorem 14, Corollary 15, Remark 16). [PDF](https://www.jmlr.org/papers/volume11/jaksch10a/jaksch10a.pdf)
- P. Auer, T. Jaksch and R. Ortner, "Near-optimal Regret Bounds for Reinforcement Learning", *Advances in Neural Information Processing Systems 21* (NeurIPS 2008), Definition 1 (the extended abstract). [PDF](https://proceedings.neurips.cc/paper_files/paper/2008/file/e4a6222cdb5b34375400904f03d8e6a5-Paper.pdf)
