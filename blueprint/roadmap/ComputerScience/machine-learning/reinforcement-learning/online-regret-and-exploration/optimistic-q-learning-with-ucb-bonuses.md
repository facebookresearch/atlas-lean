# Q-learning with upper-confidence exploration bonuses

Optimistic Q-learning keeps one table of Q-values per stage, initialized at $H$, acts greedily with respect to it, and after each step moves the visited entry toward the observed reward plus the next state's value plus an exploration bonus, with learning rate $\alpha_t = (H+1)/(H+t)$ at the $t$-th visit. It stores no transition model.

The setting is the [online episodic protocol](online-episodic-learning-and-regret.md) for an [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) with stage-dependent kernels $P_h$ and deterministic rewards $r_h \in [0, 1]$; the initial state of each episode may be chosen by an adversary. Let $T = KH$, $p \in (0, 1)$ and $\iota = \log(SAT/p)$.

The algorithm maintains $Q_h(x, a)$, $V_h(x)$ and visit counts $N_h(x, a)$ for every $(x, a, h)$, initialized by $Q_h \equiv H$, $V_h \equiv H$ and $N_h \equiv 0$ for $h \le H$, and keeps $V_{H+1} \equiv 0$; thus $V_h(x) = \min\{H, \max_{a'} Q_h(x, a')\}$ holds at every state $x$ at all times, an unvisited state keeping the optimistic value $H$. In each episode, at each step $h = 1, \dots, H$ it observes $x_h$, takes $a_h \in \arg\max_{a'} Q_h(x_h, a')$, observes $x_{h+1}$, and updates

$$
t = N_h(x_h, a_h) \leftarrow N_h(x_h, a_h) + 1, \qquad Q_h(x_h, a_h) \leftarrow (1 - \alpha_t)\, Q_h(x_h, a_h) + \alpha_t \big[r_h(x_h, a_h) + V_{h+1}(x_{h+1}) + b_t\big],
$$

$$
V_h(x_h) \leftarrow \min\Big\{H,\ \max_{a'} Q_h(x_h, a')\Big\}, \qquad \alpha_t = \frac{H + 1}{H + t}.
$$

- UCB-Hoeffding: $b_t = c\sqrt{H^3\iota/t}$ for an absolute constant $c > 0$.
- UCB-Bernstein: with $W_t$ the empirical variance of the $t$ observed next-state values $V_{h+1}(x_{h+1})$ at the triple $(x, a, h)$, constants $c_1, c_2 > 0$, $\beta_0 = 0$ and

$$
\beta_t = \min\Big\{c_1\Big(\sqrt{\tfrac{H}{t}(W_t + H)\iota} + \tfrac{\sqrt{H^7 SA}\,\iota}{t}\Big),\ c_2\sqrt{\tfrac{H^3\iota}{t}}\Big\},
$$

the bonus is $b_1 = \beta_1/2$ and $b_t = (\beta_t - (1 - \alpha_t)\beta_{t-1})/(2\alpha_t)$ for $t \ge 2$, computable online from running sums of $V_{h+1}(x_{h+1})$ and its square.

## Depends on

- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)
- [Online episodic learning and regret](online-episodic-learning-and-regret.md)

## Proof depends on

None.

## Expansion

The algorithm uses $O(SAH)$ memory, which makes it model-free in the sense of Jin, Allen-Zhu, Bubeck and Jordan: its space is $o(S^2AH)$, sublinear in the size of a transition model. Unrolling the update shows that after $t$ visits $Q_h(x, a) = \alpha_t^0 H + \sum_{i=1}^{t} \alpha_t^i [r_h(x, a) + V_{h+1}^{k_i}(x_{h+1}^{k_i}) + b_i]$, a weighted average with the [learning-rate weights](learning-rate-weights-of-optimistic-q-learning.md) $\alpha_t^i$, where $k_i$ is the episode of the $i$-th visit. The rate $\alpha_t = (H+1)/(H+t)$ keeps roughly the last $1/H$ fraction of the visits, which is what avoids a regret exponential in $H$; the rate $1/t$ would weight all visits equally, including early ones based on poor estimates of $V_{h+1}$. With the definition of $b_t$ in the Bernstein variant, $\beta_t = 2\sum_{i=1}^t \alpha_t^i b_i$. Jin, Allen-Zhu, Bubeck and Jordan also recall that Q-learning with $\varepsilon$-greedy exploration and zero initialization can need a number of episodes exponential in $H$.

## Sources

- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", *Advances in Neural Information Processing Systems 31* (NeurIPS 2018), Algorithm 1 (UCB-Hoeffding), the learning rate (3.1), Definition 1 (model-free) and the update (4.3) in Section 4. [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf)
- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", full version arXiv:1807.03765v1, Appendix C: the empirical variance (C.1), the definitions (C.2) and (C.3) of $\beta_t$ and $b_t$, and Algorithm 2 (UCB-Bernstein). [arXiv](https://arxiv.org/abs/1807.03765v1)
