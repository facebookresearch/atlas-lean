# Law of total variance for episodic returns

Along an episode played from a fixed initial state by a deterministic Markov policy, with deterministic rewards, the expected sum over stages of the one-step variances of the next-state value equals the variance of the episode's return. With rewards in $[0,1]$ it is therefore at most $H^2$, not the $H^3$ obtained by bounding each of the $H$ one-step variances by $H^2$.

Let $M$ be an [episodic MDP](episodic-mdp-with-stage-dependent-transitions.md) with deterministic rewards $r_h \in [0, 1]$, let $\pi$ be a deterministic Markov policy, fix an initial state $x_1$ and let $x_1, x_2, \dots, x_{H+1}$ be the states of an episode played by $\pi$, so that $x_{h+1} \sim P_h(\cdot \mid x_h, \pi_h(x_h))$. For $V : \mathcal{S} \to \mathbb{R}$ write the next-state variance

$$
[\mathbb{V}_h V](x, a) = \sum_{y} P_h(y \mid x, a)\, V(y)^2 - \big([P_h V](x, a)\big)^2 .
$$

Then

$$
\mathbb{E}\Big[\Big(\sum_{h=1}^{H} r_h(x_h, \pi_h(x_h)) - V_1^\pi(x_1)\Big)^2\Big] = \mathbb{E}\Big[\sum_{h=1}^{H} [\mathbb{V}_h V_{h+1}^\pi](x_h, \pi_h(x_h))\Big],
$$

and both sides are at most $H^2$.

## Depends on

- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)

## Proof depends on

None.

## Expansion

Write $G = \sum_h r_h(x_h, \pi_h(x_h))$ and $V_h = V_h^\pi$. The Bellman equation $V_h(x_h) = r_h(x_h, \pi_h(x_h)) + [P_h V_{h+1}](x_h, \pi_h(x_h))$ and $V_{H+1} = 0$ make the sum telescope:

$$
G - V_1(x_1) = \sum_{h=1}^{H} \big(r_h(x_h, \pi_h(x_h)) + V_{h+1}(x_{h+1}) - V_h(x_h)\big) = \sum_{h=1}^{H} \big(V_{h+1}(x_{h+1}) - [P_h V_{h+1}](x_h, \pi_h(x_h))\big).
$$

The summands are martingale differences for the filtration of the trajectory, so the cross terms of the square have expectation zero, and the conditional second moment of the $h$-th summand given $x_h$ is $[\mathbb{V}_h V_{h+1}](x_h, \pi_h(x_h))$. The bound $H^2$ holds because $G$ and $V_1(x_1) = \mathbb{E}[G]$ both lie in $[0, H]$.

In regret analyses this identity is applied to the policies $\pi_k$ actually played. Jin, Allen-Zhu, Bubeck and Jordan combine it with a martingale concentration argument to show that, with probability at least $1 - p$, the realized sum $\sum_{k \le K} \sum_{h \le H} [\mathbb{V}_h V_{h+1}^{\pi_k}](x_h^k, a_h^k)$ is at most $c(HT + H^3\iota)$, with $T = KH$, $\iota = \log(SAT/p)$ and an absolute constant $c$ (their Lemma C.5); Azar, Osband and Munos use the stationary form with Freedman's inequality in the same way. This is what lets Bernstein-type bonuses save a factor $\sqrt{H}$ over Hoeffding-type bonuses in the regret bounds of UCBVI and of optimistic Q-learning. Azar, Osband and Munos attribute the recursive use of the law of total variance in Markov decision processes to Munos and Moore, to Azar, Munos and Kappen, and to Lattimore and Hutter.

## Sources

- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", full version arXiv:1807.03765v1, Appendix C: the variance operator before (C.1), Lemma C.5 and the first display of its proof (this identity and the bound $H^2$); NeurIPS 2018 refers to the same lemma in Section 3. [arXiv](https://arxiv.org/abs/1807.03765v1)
- M. G. Azar, I. Osband and R. Munos, "Minimax Regret Bounds for Reinforcement Learning", ICML 2017, PMLR 70; arXiv:1703.05449v2, Section 5 (sketch of the proof of Theorem 2, the law-of-total-variance step) and the appendix identity labelled the LTV equation in the bound on the sums $W_{k,h}$ (stationary transitions). [arXiv](https://arxiv.org/abs/1703.05449v2)
