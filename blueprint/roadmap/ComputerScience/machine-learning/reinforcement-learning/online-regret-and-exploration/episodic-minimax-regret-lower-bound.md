# Minimax regret lower bound for episodic MDPs with stage-dependent transitions

Every learning algorithm has expected regret at least $\frac{1}{48\sqrt6}\sqrt{H^3SAT}$ after $T \ge HSA$ episodes on some episodic MDP with $S$ states, $A$ actions, horizon $H$, stage-dependent transitions and rewards in $[0,1]$, when $A \ge 2$, $S \ge 6$, $S$ and $A$ fit a full $A$-ary tree and $H$ is at least three times its depth. Here $T$ counts episodes, not steps.

Assume $S \ge 6$, $A \ge 2$, that $S = 3 + (A^d - 1)/(A - 1)$ for an integer $d$, and that $H \ge 3d$. Consider [episodic MDPs](episodic-mdp-with-stage-dependent-transitions.md) with $S$ states, $A$ actions, horizon $H$, stage-dependent kernels $p_h$, rewards $r_h(s, a) \in [0, 1]$ and an initial distribution $\mu$, and the [expected regret](online-episodic-learning-and-regret.md) after $T$ episodes

$$
\mathcal{R}_T(\pi, M) = \mathbb{E}_{\pi, M}\Big[\sum_{t=1}^{T} \big(\rho^\star - \rho^{\pi, t}\big)\Big],
$$

where $\rho^\star = \mathbb{E}_{s \sim \mu}[V^\star(s)]$ and $\rho^{\pi,t}$ is the expected value, over $s \sim \mu$, of the possibly history-dependent algorithm $\pi$ in episode $t$ given the history before it. Then for every algorithm $\pi$ and every number of episodes $T \ge HSA$ there is such an MDP $M_{\pi,T}$, depending on both $\pi$ and $T$, with

$$
\mathcal{R}_T(\pi, M_{\pi,T}) \ge \frac{1}{48\sqrt{6}} \sqrt{H^3 S A T} .
$$

## Depends on

- [Online episodic learning and regret](online-episodic-learning-and-regret.md)
- [Episodic Markov decision process with stage-dependent transitions](episodic-mdp-with-stage-dependent-transitions.md)
- [History-dependent randomized policies and trajectory laws](../../../heuristic-search-and-planning/markov-decision-processes/history-dependent-randomized-policies-and-trajectory-laws.md)

## Proof depends on

- [Data-processing inequality for the Kullback–Leibler divergence](../../../../InformationTheory/information-inequalities/data-processing-inequality/kl-div-map-le.md)
- [Binary Pinsker inequality on the closed interval](../../../../InformationTheory/information-inequalities/binary-pinsker-of-mem-icc.md)

## Expansion

With $T$ episodes there are $TH$ steps, so the bound reads $\Omega(\sqrt{H^2 S A \cdot TH})$ in steps; it is the bound Jin, Allen-Zhu, Bubeck and Jordan sketched, here with a complete proof and a different construction. In the same paper, Appendix D drops the arithmetic condition on $S$: if $S \ge 11$, $A \ge 4$ and $H \ge 6$, then for every $T \ge HSA$ some MDP $M_{\pi,T}$ has $\mathcal{R}_T(\pi, M_{\pi,T}) \ge c_3\sqrt{\min(S, A^{H/3 - 2})}\sqrt{H^3AT}$ with an absolute constant $c_3$ (Theorem 12). With stage-independent transitions the same method gives order $\sqrt{H^2SAT}$ only (Appendix C), which is why upper bounds for stationary models, such as the [Bernstein bound for UCBVI](ucbvi-bernstein-regret-bound.md), can be smaller.

The hard instances behave like a bandit with about $HSA$ arms. The agent starts in a waiting state from which it may leave at any stage up to $\bar H$; it then descends a full $A$-ary tree of depth $d - 1$ to a leaf, and from the leaf an action moves it to an absorbing good state, the only rewarding state (reward $1$ per stage once a fixed stage is reached), or to an absorbing bad state with reward $0$. All leaf actions lead to the good state with probability $1/2$, except one triple (stage, leaf, action) that adds $\varepsilon$. The proof compares each instance with the reference instance without the extra $\varepsilon$: the Kullback–Leibler divergence between the two laws of $T$ episodes equals the expected number of plays of the special triple times a Bernoulli divergence, the data-processing inequality and Pinsker's inequality bound how much the expected number of plays can change, and averaging over the $\Theta(\bar H SA)$ triples with $\bar H = H/3$ gives the bound. The gap $\varepsilon$ is tuned to $T$, of order $\sqrt{\bar H SA/T}$, so the hard instance changes with $T$; no single MDP is claimed to be hard for all $T$.

The step that writes the Kullback–Leibler divergence between the laws of the $T$ episodes as a sum over stage-state-action triples of expected visit counts times one-step divergences (Lemma 5 of the source) has no page in the graph; the [divergence decomposition for stochastic bandits](../multi-armed-bandits/divergence-decomposition-for-stochastic-bandits.md) is its one-state analogue, not the statement used. It is a missing proof prerequisite. So is Lemma 6 in the form the proof uses it, $\mathrm{kl}(\mathbb{E}_{P}[Z], \mathbb{E}_{Q}[Z]) \le \mathrm{KL}(P, Q)$ for every measurable $Z$ with values in $[0, 1]$, with $\mathrm{kl}$ the Bernoulli divergence (Lemma 1 of Garivier, Ménard and Stoltz); the linked data-processing inequality for pushforwards gives it only after a further randomization step. A good expansion also gives pages to the hard class $\mathcal{C}_{\bar H, \varepsilon}$ of Section 3.1 with its regret computation, and to the proof of Theorem 9 that optimizes $\varepsilon$ and $\bar H$.

The companion sample-complexity result in the same paper (Theorem 7) states that an $(\varepsilon, \delta)$-PAC algorithm for best-policy identification needs at least $\frac{1}{3456}\frac{H^3SA}{\varepsilon^2}\log\frac1\delta$ episodes in expectation on some such MDP, for $0 < \varepsilon \le H/24$, $H \ge 4$ and $0 < \delta \le 1/16$.

## Sources

- O. D. Domingues, P. Ménard, E. Kaufmann and M. Valko, "Episodic Reinforcement Learning in Finite MDPs: Minimax Lower Bounds Revisited", *Proceedings of the 32nd International Conference on Algorithmic Learning Theory* (ALT 2021), PMLR 132: Definition 1 (expected regret after $T$ episodes), Assumption 1, Section 3.1 (hard instances), Lemmas 5 and 6, Theorem 9 and its proof, Theorem 7, Appendix C (stage-independent transitions) and Theorem 12 in Appendix D. [PDF](https://proceedings.mlr.press/v132/domingues21a/domingues21a.pdf)
- C. Jin, Z. Allen-Zhu, S. Bubeck and M. I. Jordan, "Is Q-learning Provably Efficient?", NeurIPS 2018, Theorem 4 (the lower bound $\Omega(\sqrt{H^2SAT})$ in steps, with a proof sketch in Appendix D of the full version arXiv:1807.03765v1). [PDF](https://proceedings.neurips.cc/paper_files/paper/2018/file/d3b1fb02964aa64e257f9f26a31f72cf-Paper.pdf)
