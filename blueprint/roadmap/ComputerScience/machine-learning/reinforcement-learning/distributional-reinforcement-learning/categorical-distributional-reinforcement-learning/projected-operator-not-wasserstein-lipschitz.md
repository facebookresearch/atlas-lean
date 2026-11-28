# The projected categorical operator is not Lipschitz in the maximal Wasserstein metric

For $1 < p < \infty$ and every discount $\gamma \in (0,1)$, the projected categorical operator can expand maximal Wasserstein distances by an arbitrarily large factor. It is not a contraction in $\bar d_p$.

Let $1 < p < \infty$, $\gamma \in (0,1)$ and a grid $z_1 < \dots < z_K$ with $K \ge 2$; write $\Delta = z_2 - z_1$ and $c = (z_1 + z_2)/2$. Take the MDP with one state $x$, one action $a$ and the [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) $\delta_c \otimes \delta_x$, so the reward is the constant $c$. Let $\Pi_{\mathcal{C}}$ be the [categorical projection](../categorical-distributional-reinforcement-learning/categorical-projection.md), $\mathcal{T}^\pi$ the [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md) of the only policy, and $\bar d_p$ the [maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md). For $0 < h < \Delta/(2\gamma)$ let $\eta = \delta_0$ and $\mu = \delta_h$. Then

$$\bar d_p(\eta, \mu) = h, \qquad \bar d_p(\Pi_{\mathcal{C}} \mathcal{T}^\pi \eta, \Pi_{\mathcal{C}} \mathcal{T}^\pi \mu) = (\gamma h)^{1/p} \Delta^{1 - 1/p}.$$

The ratio $\gamma^{1/p} \Delta^{1 - 1/p} h^{1/p - 1}$ tends to $\infty$ as $h \to 0$. So for every $L \ge 0$ there are $\eta, \mu \in \mathscr{P}_p(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ with $\bar d_p(\Pi_{\mathcal{C}} \mathcal{T}^\pi \eta, \Pi_{\mathcal{C}} \mathcal{T}^\pi \mu) > L \, \bar d_p(\eta, \mu)$.

## Depends on

- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)
- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md)

## Proof depends on

- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md)
- [Wasserstein distance between Dirac masses](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-dirac.md)
- [Every coupling bounds the Wasserstein distance](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-le-of-is-coupling.md)
- [Wasserstein distance of order p](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)

## Expansion

$\bar d_p(\delta_0, \delta_h) = h$ is the [distance between Dirac masses](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-dirac.md). The images are $\mathcal{T}^\pi \eta = \delta_c$ and $\mathcal{T}^\pi \mu = \delta_{c + \gamma h}$, and $z_1 < c < c + \gamma h < z_2$. Their projections are $\frac12 \delta_{z_1} + \frac12 \delta_{z_2}$ and $(\frac12 - \frac{\gamma h}{\Delta}) \delta_{z_1} + (\frac12 + \frac{\gamma h}{\Delta}) \delta_{z_2}$. For two laws on $\{z_1, z_2\}$ whose masses at $z_1$ differ by $s$, every coupling moves at least mass $s$ across distance $\Delta$, and moving exactly that mass is a coupling; so $W_p^p = s \Delta^p$ ([every coupling bounds the distance](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-le-of-is-coupling.md) for the upper bound). With $s = \gamma h/\Delta$ this gives the display.

Rowland and coauthors prove their Lemma 2 by showing that $\Pi_{\mathcal{C}}$ alone expands $\delta_{1/4}, \delta_{3/4}$ on the grid $\{0, 1\}$: the $d_p$-distance goes from $\frac12$ to $2^{-1/p} > \frac12$. They call that enough, but embedding those Dirac masses in a one-state MDP gives the ratio $\gamma \, 2^{1 - 1/p}$, which exceeds $1$ only when $\gamma > 2^{1/p - 1}$. The family above, with inputs approaching each other, covers every $\gamma \in (0,1)$. The statement is existential: it exhibits one MDP. At $\gamma = 0$ the operator is constant. For $p = 1$ the same computation gives the ratio $\gamma$; the source's remark that contractivity in $\bar d_1$ is maintained is not proved there and is not stated here.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.1, Lemma 2, proved in Appendix C.
