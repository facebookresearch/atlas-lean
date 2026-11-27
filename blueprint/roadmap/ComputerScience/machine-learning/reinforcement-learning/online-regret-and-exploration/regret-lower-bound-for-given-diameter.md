# Regret lower bound for MDPs with a given diameter

For every learning algorithm and all $S, A \ge 10$, $D \ge 20\log_A S$ and $T \ge DSA$, some MDP with $S$ states, $A$ actions and diameter $D$ forces expected regret at least $0.015\sqrt{DSAT}$ after $T$ steps, from every initial state.

Let $\mathfrak{A}$ be any learning algorithm for the [average-reward regret](regret-against-optimal-average-reward.md) setting, and let $S, A \ge 10$, $D \ge 20\log_A S$ and $T \ge DSA$ be natural numbers. Then there is an MDP $M$, depending on $\mathfrak{A}$, $S$, $A$, $D$ and $T$, with $S$ states, $A$ actions and [diameter](diameter-of-an-mdp.md) $D$ such that, for every initial state $s$,

$$
\mathbb{E}\big[\Delta(M, \mathfrak{A}, s, T)\big] \ge 0.015\sqrt{DSAT}.
$$

## Depends on

- [Regret against the optimal average reward](regret-against-optimal-average-reward.md)
- [Diameter of a Markov decision process](diameter-of-an-mdp.md)

## Proof depends on

- [Csiszár–Kullback–Pinsker inequality for strictly positive distributions](../../../../InformationTheory/information-inequalities/csiszar-kullback-pinsker.md)

## Expansion

The condition $D \ge 20\log_A S$ is compatible with the fact that every MDP with $S$ states and $A \ge 2$ actions has diameter at least $\log_A S - 3$. Compared with the [UCRL2 upper bound](ucrl2-regret-bound.md) of order $DS\sqrt{AT}$, a factor $\sqrt{DS}$ is open. In the episodic setting the horizon plays the role of $D$; there the [minimax lower bound for episodic MDPs](episodic-minimax-regret-lower-bound.md) is the analogue, larger by a factor $\sqrt{H}$ for stage-dependent transitions.

The construction starts from a two-state MDP with states $s_\circ$ (reward $0$) and $s_p$ (reward $1$) and $\lfloor (A-1)/2 \rfloor$ actions: every action moves from $s_\circ$ to $s_p$ with probability $\delta = 4/D$, except one good action that does so with probability $\delta + \varepsilon$, and $s_p$ returns to $s_\circ$ with probability $\delta$. Playing a non-good action at $s_\circ$ costs average reward of order $\varepsilon/\delta$ per step, and telling the good action apart needs of order $\delta/\varepsilon^2$ visits to $s_\circ$. About $S/2$ copies of this MDP, of which only one contains a good action, are joined by a tree of the remaining actions so that the diameter stays at most $D$. The learner then faces a bandit problem with about $SA$ arms, and the change-of-measure argument of the lower bound for nonstochastic bandits of Auer, Cesa-Bianchi, Freund and Schapire, adapted with a bound on the expected number of visits (Lemma 13) whose bandit original rests on Pinsker's inequality, gives the result, in the spirit of the [minimax lower bound for bandits](../multi-armed-bandits/minimax-regret-lower-bound-for-gaussian-bandits.md); when $D < 12$ a separate bandit construction is used. Pinsker's inequality enters through the bound $|\mathbb{E}_a f - \mathbb{E}_{\mathrm{unif}} f| \le \frac B2\sqrt{2\log 2 \cdot \mathrm{KL}}$ for functions of the state sequence (Appendix E, (49)), applied to laws that are strictly positive because every transition probability lies strictly between $0$ and $1$. The chain rule that expands that divergence over the steps of the state sequence (Appendix E, (50)) has no page in the graph and is a missing proof prerequisite. A good expansion also gives pages to Lemma 13 (for every function $f$ of the state sequences $s \in \{s_\circ, s_p\}^{T+1}$ observed in the two-state MDP $M'$ with values in $[0, B]$, every $0 < \delta \le 1/2$, every $0 \le \varepsilon \le 1 - 2\delta$ and every $a \in \{1, \dots, kA'\}$, $\mathbb{E}_a[f(s)] \le \mathbb{E}_{\mathrm{unif}}[f(s)] + \frac{B}{2}\frac{\varepsilon}{\sqrt\delta}\sqrt{2\mathbb{E}_{\mathrm{unif}}[N_\circ^*]}$, proved in Appendix E), to the elementary inequality of Lemma 20 used there, and to the construction of Section 6 with the joining tree and the separate construction of footnote 11. The displayed Lemma 13 bound is restricted here to positive $\delta$, as its factor $\varepsilon/\sqrt\delta$ requires; the two-state lower-bound construction uses $\delta=4/D>0$.

## Sources

- T. Jaksch, R. Ortner and P. Auer, "Near-optimal Regret Bounds for Reinforcement Learning", *Journal of Machine Learning Research* 11 (2010), 1563–1600: Theorem 5 with footnote 5, Section 6 (the proof, Figure 3 and Lemma 13, including footnote 11 for small $D$), Appendix E (proof of Lemma 13, (49) and (50)) with Lemma 20, Section 8 and Corollary 15. [PDF](https://www.jmlr.org/papers/volume11/jaksch10a/jaksch10a.pdf)
- P. Auer, T. Jaksch and R. Ortner, "Near-optimal Regret Bounds for Reinforcement Learning", *Advances in Neural Information Processing Systems 21* (NeurIPS 2008), Theorem 5 there (the lower bound with an unspecified constant) and its proof sketch. [PDF](https://proceedings.neurips.cc/paper_files/paper/2008/file/e4a6222cdb5b34375400904f03d8e6a5-Paper.pdf)
