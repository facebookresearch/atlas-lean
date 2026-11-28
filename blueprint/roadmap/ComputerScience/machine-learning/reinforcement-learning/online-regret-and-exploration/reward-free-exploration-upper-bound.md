# Sample complexity of reward-free exploration

In a tabular episodic MDP with stage-dependent transitions, for $0 < \varepsilon \le H$ some reward-free exploration algorithm uses $c[H^5S^2A\iota/\varepsilon^2 + S^4AH^7\iota^3/\varepsilon]$ exploration episodes, with $\iota = \log(SAH/(p\varepsilon))$, and then with probability at least $1-p$ returns $\varepsilon$-optimal policies for any number of adaptively chosen reward functions in $[0,1]$.

Consider [reward-free exploration](reward-free-exploration.md) in [episodic MDPs](episodic-mdp-with-stage-dependent-transitions.md) with $S$ states, $A$ actions, horizon $H$, stage-dependent transitions and an initial distribution $\mu$, with reward functions $r_h : \mathcal{S} \times \mathcal{A} \to [0, 1]$ supplied after exploration. There are an absolute constant $c > 0$ and a reward-free exploration algorithm, whose only inputs are $S$, $A$, $H$, the accuracy $\varepsilon$ and the failure probability $p$, such that for every $0 < \varepsilon \le H$, every $p \in (0, 1)$ and every such MDP, with probability at least $1 - p$ the algorithm outputs, for an arbitrary number of adaptively chosen reward functions $r$, policies $\hat\pi$ with $\mathbb{E}_{s_1 \sim \mu}[V_1^\star(s_1; r) - V_1^{\hat\pi}(s_1; r)] \le \varepsilon$, after an exploration phase of at most

$$
c\left[\frac{H^5 S^2 A\, \iota}{\varepsilon^2} + \frac{S^4 A H^7 \iota^3}{\varepsilon}\right], \qquad \iota = \log\frac{SAH}{p\varepsilon},
$$

episodes.

## Depends on

- [Reward-free exploration](reward-free-exploration.md)
- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)

## Proof depends on

- [Freedman's maximal inequality for adaptive supermartingales](../../../../Probability/concentration-inequalities/adaptive-martingale-tail-bounds/freedman-maximal-inequality.md)

## Expansion

The leading term $H^5S^2A/\varepsilon^2$ is tight in $S$, $A$ and $\varepsilon$ up to logarithmic factors and lower-order terms by the [reward-free lower bound](reward-free-exploration-lower-bound.md) of order $S^2AH^2/\varepsilon^2$, which leaves a gap of $H^3$. It is larger than the order $SAH^3/\varepsilon^2$ of a single known reward, as in the sample complexity derived from the [regret without burn-in](minimax-regret-without-burn-in.md): one dataset must serve every reward function. Values are in $[0, H]$ here, since each $r_h$ is in $[0, 1]$.

The algorithm has two phases. For each pair $(s, h)$, exploration runs an online regret-minimizing algorithm, EULER of Zanette and Brunskill applied with $SH$ states, on the reward $\mathbb{1}[s' = s, h' = h]$, whose optimal policy maximizes the probability of reaching $s$ at step $h$; it keeps the $N_0$ policies produced, with the action at $(s, h)$ itself made uniform. It then plays policies drawn uniformly from the union of these sets for $N$ episodes. With $N_0 \ge cS^2AH^4\iota_0^3/\delta$, $\iota_0 = \log(SAH/(p\delta))$, the $N$ trajectories are i.i.d. from a distribution $\lambda$ with step-$h$ state-action marginals $\lambda_h$ such that $\max_{a,\pi} P_h^\pi(s, a)/\lambda_h(s, a) \le 2SAH$ at every $\delta$-significant $(s, h)$ (Theorem 3.3; the source writes $\mu$ and $\mu_h$ for this data distribution, while $\mu$ here is the initial distribution). Planning estimates $\hat P$ from the dataset and runs any approximate solver, such as value iteration or natural policy gradient, on $(\hat P, r)$. With $\delta = \varepsilon/(2SH^2)$ and $N \ge cH^5S^2A\iota/\varepsilon^2$, simultaneously for all reward functions and all policies, values under $\hat P$ and under $P$ from $\mu$ differ by at most $\varepsilon$, so the planner's output is $3\varepsilon$-optimal (Theorem 3.5 and Lemma 3.6); the proof combines Bernstein's inequality for averages of the i.i.d. samples, the deterministic-variance case of Freedman's inequality, with a covering of deterministic policies and their values. Rescaling $\varepsilon$ gives the theorem.

Two proof steps have no page in the graph. The exploration guarantee rests on the regret-type guarantee of EULER (Zanette and Brunskill, ICML 2019), restated as Lemma 3.4 for stage-dependent MDPs through the reduction to $SH$ states: the average of the $N_0$ output policies is suboptimal by at most $c(\sqrt{SAH\iota_0' \mathbb{E}V_1^\star/N_0} + S^2AH^4(\iota_0')^3/N_0)$, where here $\iota_0' = \log(SAHN_0/p)$, not the $\iota_0$ of Theorem 3.3. The planning analysis uses the finite-horizon value-difference lemma (Lemma E.15 of Dann, Lattimore and Brunskill, restated as Lemma C.1 in the appendix of arXiv:2002.02794v1), which writes $\hat V_1^\pi - V_1^\pi$ as an expected sum over stages of $(\hat P_h - P_h)\hat V_{h+1}^\pi$ along trajectories of $\pi$ in the true MDP; the graph's [simulation lemma](../simulation-lemma/stoch-value-sub-stoch-value-eq.md) is its discounted counterpart, not this statement. Both are missing proof prerequisites. A good expansion also gives pages to the paper's own steps: Theorem 3.3 (the exploration guarantee, from Lemma 3.4), Lemma 3.6 and Theorem 3.5 (the planning guarantee), and the concentration Lemma C.2 of the appendix, which bounds, simultaneously for every function $G : \mathcal{S} \to [0, H]$ and every deterministic policy $\nu$, the weighted squared error $\mathbb{E}_{\lambda_h}\big[\lvert(\hat P_h - P_h)G(s, a)\rvert^2\,\mathbb{1}\{a = \nu(s)\}\big]$ by $O(H^2S\log(AHN/p)/N)$ through Bernstein's inequality and a covering argument; the proof of Theorem 3.1 in Appendix C.3 combines them.

## Sources

- C. Jin, A. Krishnamurthy, M. Simchowitz and T. Yu, "Reward-Free Exploration for Reinforcement Learning", *Proceedings of the 37th International Conference on Machine Learning* (ICML 2020), PMLR 119: Theorem 3.1, Algorithm 2 (Reward-free RL-Explore) with Theorem 3.3 and Lemma 3.4 (exploration phase), Algorithm 3 (Reward-free RL-Plan) with Theorem 3.5 and Lemma 3.6 (planning phase), Proposition 3.7 (natural policy gradient, Algorithm 4, as a solver); the appendix of arXiv:2002.02794v1, Lemmas C.1 and C.2 and Section C.3 (proof of Theorem 3.1). [PDF](https://proceedings.mlr.press/v119/jin20d/jin20d.pdf)
