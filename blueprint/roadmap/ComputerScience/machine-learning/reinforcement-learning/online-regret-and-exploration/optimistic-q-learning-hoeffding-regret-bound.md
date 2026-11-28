# Regret bound for Q-learning with Hoeffding bonuses

In an episodic MDP with stage-dependent transitions, rewards in $[0,1]$ and adversarial initial states, Q-learning with learning rate $(H+1)/(H+t)$ and bonus $c\sqrt{H^3\iota/t}$ has regret $O(\sqrt{H^4SAT\iota})$ with probability at least $1-p$, where $T = KH$ is the number of steps and $\iota = \log(SAT/p)$.

There is an absolute constant $c > 0$ such that the following holds, with an absolute constant in the $O(\cdot)$ below. Let $p \in (0, 1)$ and let $M$ be any [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) with $S$ states, $A$ actions, horizon $H$, stage-dependent transition kernels $P_1, \dots, P_H$ and deterministic rewards $r_h \in [0, 1]$, played for $K$ episodes in the [online episodic protocol](online-episodic-learning-and-regret.md) with initial states chosen by an adversary, and let $T = KH$. Then [Q-learning with the UCB-Hoeffding bonus](optimistic-q-learning-with-ucb-bonuses.md) $b_t = c\sqrt{H^3\iota/t}$, $\iota = \log(SAT/p)$, which uses only $S$, $A$, $H$, $T$ and $p$ and the observed transitions and rewards, satisfies with probability at least $1 - p$

$$
\mathrm{Regret}(K) = \sum_{k=1}^{K} \big(V_1^\star(x_1^k) - V_1^{\pi_k}(x_1^k)\big) \le O\big(\sqrt{H^4 S A T \iota}\big).
$$

## Depends on

- [Q-learning with upper-confidence exploration bonuses](optimistic-q-learning-with-ucb-bonuses.md)
- [Online episodic learning and regret](online-episodic-learning-and-regret.md)

## Proof depends on

- [Learning-rate weights of optimistic Q-learning](learning-rate-weights-of-optimistic-q-learning.md)
- [Azuma-Hoeffding inequality for adaptive processes with bounded conditional ranges](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/azuma-hoeffding-bounded-conditional-ranges.md)

## Expansion

In episodes, $\sqrt{H^4SAT} = \sqrt{H^5SAK}$. The bound holds for every $K$ without a burn-in term: the proof first gives $O(H^2SA + \sqrt{H^4SAT\iota})$ and removes $H^2SA$ by comparing with the trivial bound $\mathrm{Regret}(K) \le HK = T$. Against the [stage-dependent lower bound](episodic-minimax-regret-lower-bound.md) of order $\sqrt{H^2SAT}$ it loses a factor $H$.

The proof has three steps. First, unrolling the update gives $(Q_h^k - Q_h^\star)(x, a) = \alpha_t^0(H - Q_h^\star(x, a)) + \sum_{i=1}^t \alpha_t^i[(V_{h+1}^{k_i} - V_{h+1}^\star)(x_{h+1}^{k_i}) + ((\hat P_h^{k_i} - P_h)V_{h+1}^\star)(x, a) + b_i]$, where $\hat P_h^{k_i}V(x, a) = V(x_{h+1}^{k_i})$ is the one-sample estimate. Second, the Azuma–Hoeffding inequality at the stopping times of the visits, with a union bound over $(x, a, h)$ and the number of visits, bounds the weighted noise by $c\sqrt{H^3\iota/t}$, which the accumulated bonus dominates; backward induction on $h$ then gives optimism $Q_h^k \ge Q_h^\star$ and an upper bound on $Q_h^k - Q_h^\star$. Third, with $\delta_h^k = (V_h^k - V_h^{\pi_k})(x_h^k)$, regrouping the weighted sums with item 3 of the learning-rate lemma yields

$$
\sum_{k} \delta_h^k \le SAH + \Big(1 + \frac{1}{H}\Big) \sum_k \delta_{h+1}^k + \sum_k \big(\beta_{n_h^k} + \xi_{h+1}^k\big),
$$

which unrolls over $h$ with a factor $(1 + 1/H)^H \le e$. The bonuses sum to $O(\sqrt{H^4SAT\iota})$ by the pigeonhole principle: for counts $N(x, a)$ summing to $K$, the sum $\sum_{x,a}\sum_{n \le N(x,a)} n^{-1/2}$ is largest when the counts are equal, which makes it $O(\sqrt{SAK})$. The martingale terms $\xi$ sum to $O(H\sqrt{T\iota})$.

## Sources

- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", *Advances in Neural Information Processing Systems 31* (NeurIPS 2018), Theorem 2 (Hoeffding), Section 4 with Lemmas 4.2 and 4.3, the recursion (4.7) and the pigeonhole step (4.8). In the full version arXiv:1807.03765v1 the same theorem is numbered Theorem 1. [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf)
