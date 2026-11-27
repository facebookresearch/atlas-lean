# Episodic Markov decision process with stage-dependent transitions

A tabular episodic MDP with horizon $H$ has finite state and action sets and, for each stage $h = 1, \dots, H$, its own transition kernel $P_h$ and reward function $r_h$ with values in $[0,1]$; an episode runs the $H$ stages once. It is called stationary, or time-homogeneous, when $P_h$ and $r_h$ do not depend on $h$.

Precisely, the model $\mathrm{MDP}(\mathcal{S}, \mathcal{A}, H, P, r)$ consists of a finite state set $\mathcal{S}$ with $S = |\mathcal{S}|$, a finite action set $\mathcal{A}$ with $A = |\mathcal{A}|$, an integer horizon $H \ge 1$, and for each stage $h \in [H] = \{1, \dots, H\}$ a transition kernel $P_h(\cdot \mid x, a)$, a probability distribution on $\mathcal{S}$ for every $(x, a) \in \mathcal{S} \times \mathcal{A}$, and a deterministic reward function $r_h : \mathcal{S} \times \mathcal{A} \to [0, 1]$.

A deterministic Markov policy is a tuple $\pi = (\pi_1, \dots, \pi_H)$ of maps $\pi_h : \mathcal{S} \to \mathcal{A}$. Started in state $x_h = x$ at stage $h$, it generates states by $x_{h'+1} \sim P_{h'}(\cdot \mid x_{h'}, \pi_{h'}(x_{h'}))$ for $h \le h' \le H$, and its value and action-value functions are

$$
V_h^\pi(x) = \mathbb{E}\Big[\sum_{h'=h}^{H} r_{h'}(x_{h'}, \pi_{h'}(x_{h'})) \,\Big|\, x_h = x\Big], \qquad Q_h^\pi(x, a) = r_h(x, a) + \mathbb{E}\Big[\sum_{h'=h+1}^{H} r_{h'}(x_{h'}, \pi_{h'}(x_{h'})) \,\Big|\, x_h = x, a_h = a\Big],
$$

with $V_{H+1}^\pi \equiv 0$. Writing $[P_h V](x, a) = \sum_{y} P_h(y \mid x, a) V(y)$ for $V : \mathcal{S} \to \mathbb{R}$, these functions obey $Q_h^\pi = r_h + P_h V_{h+1}^\pi$ and $V_h^\pi(x) = Q_h^\pi(x, \pi_h(x))$, and $0 \le V_h^\pi \le H - h + 1$. The optimal value is $V_h^\star(x) = \sup_\pi V_h^\pi(x)$, and with $V_{H+1}^\star \equiv 0$ it satisfies the Bellman optimality recursion

$$
Q_h^\star = r_h + P_h V_{h+1}^\star, \qquad V_h^\star(x) = \max_{a \in \mathcal{A}} Q_h^\star(x, a) \qquad (h = H, H-1, \dots, 1).
$$

A policy that is greedy for $Q_h^\star$ at every stage attains $V_h^\star(x)$ for every $h$ and $x$ simultaneously.

The stationary special case has $P_1 = \dots = P_H = P$ and $r_1 = \dots = r_H = r$.

## Depends on

- [Markov decision process](../../../heuristic-search-and-planning/value-iteration/mdp.md)

## Proof depends on

None.

## Expansion

The two models are not interchangeable in bounds. A stage-dependent model with $S$ states is a stationary model on the $SH$ states $(x, h)$, so a guarantee proved for stationary models transfers to stage-dependent ones only with $S$ replaced by $SH$; Jin, Allen-Zhu, Bubeck and Jordan note that this costs a factor $\sqrt{H}$ in the leading regret term of Azar, Osband and Munos, whose analysis assumes $P_1 = \dots = P_H$. Lower bounds reflect the same gap: Domingues, Ménard, Kaufmann and Valko prove a minimax regret lower bound for stage-dependent transitions that is a factor $\sqrt{H}$ larger than the one their construction gives with stage-independent transitions.

Sources also differ in normalization. Per-step deterministic rewards in $[0, 1]$, as above, give returns in $[0, H]$. Zhang, Chen, Lee and Du allow random rewards and assume only that every episode's total reward lies in $[0, H]$; Li, Wang and Yang assume per-step rewards in $[0, 1]$ with total reward at most $1$, so that their accuracy $\varepsilon$ corresponds to $H\varepsilon$ in the per-step normalization. Some sources index stages $0, \dots, H-1$. Randomized and history-dependent policies do not exceed $V^\star$, so restricting to deterministic Markov policies loses nothing in the definition of $V^\star$. The recursion is the finite-horizon dynamic programming algorithm; the [optimality of the dynamic programming algorithm](../../../heuristic-search-and-planning/optimality-of-stationary-policies/is-greatest-n-stage-value.md) treats its stationary, discounted form.

## Sources

- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", *Advances in Neural Information Processing Systems 31* (NeurIPS 2018), Section 2 (the model, the Bellman equations (2.1)) and footnote 2 (stationary versus stage-dependent transitions). [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf)
- M. G. Azar, I. Osband and R. Munos, "Minimax Regret Bounds for Reinforcement Learning", *Proceedings of the 34th International Conference on Machine Learning* (ICML 2017), PMLR 70, Section 2 and Assumption 1 (one transition distribution $P$ for all stages, deterministic rewards in $[0,1]$); arXiv:1703.05449v2. [PDF](https://proceedings.mlr.press/v70/azar17a/azar17a.pdf)
- O. D. Domingues, P. Ménard, E. Kaufmann and M. Valko, "Episodic Reinforcement Learning in Finite MDPs: Minimax Lower Bounds Revisited", *Proceedings of the 32nd International Conference on Algorithmic Learning Theory* (ALT 2021), PMLR 132, Section 2 (Markov and history-dependent policies, sufficiency of Markov policies) and Appendix C. [PDF](https://proceedings.mlr.press/v132/domingues21a/domingues21a.pdf)
- Z. Zhang, Y. Chen, J. D. Lee and S. S. Du, "Settling the Sample Complexity of Online Reinforcement Learning", arXiv:2307.13586v4, Section 2 and Assumption 1 (total reward of an episode in $[0, H]$); extended abstract in *Proceedings of the 37th Annual Conference on Learning Theory* (COLT 2024), PMLR 247; journal version in *Journal of the ACM* (2025), doi:10.1145/3733592.
- Y. Li, R. Wang and L. F. Yang, "Settling the Horizon-Dependence of Sample Complexity in Reinforcement Learning", *2021 IEEE 62nd Annual Symposium on Foundations of Computer Science* (FOCS 2021), Section II and Assumption II.1 (time-invariant transitions, total reward at most 1), doi:10.1109/FOCS52979.2021.00097.
