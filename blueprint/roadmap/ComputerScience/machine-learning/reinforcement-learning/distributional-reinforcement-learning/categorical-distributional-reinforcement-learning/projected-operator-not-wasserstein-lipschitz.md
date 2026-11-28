# The projected categorical operator is not a contraction in the maximal Wasserstein metric

For $1 < p < \infty$ the categorical projection can expand $p$-Wasserstein distances, so the projected categorical operator is in general not a contraction in $\bar d_p$.

Let $1 < p < \infty$, let $\Pi_{\mathcal{C}}$ be the [categorical projection](../categorical-distributional-reinforcement-learning/categorical-projection.md) onto the grid $\{0, 1\}$ and $W_p$ the [Wasserstein distance of order $p$](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md). Then

$$W_p(\delta_{1/4}, \delta_{3/4}) = \tfrac12, \qquad W_p(\Pi_{\mathcal{C}} \delta_{1/4}, \Pi_{\mathcal{C}} \delta_{3/4}) = 2^{-1/p} > \tfrac12.$$

Consequently, take the MDP with one state $x$, one action $a$, reward $0$ (the [reward–transition kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md) $\delta_0 \otimes \delta_x$), a discount $\gamma \in (2^{1/p - 1}, 1)$, the [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md) $\mathcal{T}^\pi$ of the only policy and the [maximal Wasserstein metric](../return-distributions-and-policy-evaluation/maximal-wasserstein-metric.md) $\bar d_p$. For $\eta = \delta_{1/(4\gamma)}$ and $\mu = \delta_{3/(4\gamma)}$,

$$\bar d_p(\eta, \mu) = \frac{1}{2\gamma} < 2^{-1/p} = \bar d_p(\Pi_{\mathcal{C}} \mathcal{T}^\pi \eta, \Pi_{\mathcal{C}} \mathcal{T}^\pi \mu),$$

so $\Pi_{\mathcal{C}} \mathcal{T}^\pi$ is not a non-expansion, and in particular not a contraction, in $\bar d_p$.

## Depends on

- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Wasserstein distance of order p](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein.md)
- [Finite MDP with a joint reward and next-state kernel](../return-distributions-and-policy-evaluation/reward-and-transition-kernel-mdp.md)
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

$W_p(\delta_{1/4}, \delta_{3/4}) = \frac12$ is the [distance between Dirac masses](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-dirac.md). The projections are $\frac34 \delta_0 + \frac14 \delta_1$ and $\frac14 \delta_0 + \frac34 \delta_1$. For two laws on $\{0, 1\}$ whose masses at $0$ differ by $s$, every coupling moves at least mass $s$ across distance $1$, and moving exactly that mass is a coupling ([every coupling bounds the distance](../../../../../MeasureTheory/optimal-transport/wasserstein-distances/wasserstein-distance/wasserstein-le-of-is-coupling.md)); so $W_p^p = s$, here $s = \frac12$, giving $2^{-1/p}$, which exceeds $\frac12$ exactly when $p > 1$. In the MDP, $\mathcal{T}^\pi \eta = (S_\gamma)_\# \eta = \delta_{1/4}$ and $\mathcal{T}^\pi \mu = \delta_{3/4}$, while $\bar d_p(\eta, \mu) = 1/(2\gamma)$; the condition $\gamma > 2^{1/p - 1}$ is $1/(2\gamma) < 2^{-1/p}$.

Rowland and coauthors state that $\Pi_{\mathcal{C}} \mathcal{T}^\pi$ is "in general" not a contraction for $p > 1$ and prove it by exhibiting the expansion of $\Pi_{\mathcal{C}}$ on $\delta_{1/4}, \delta_{3/4}$, which they call enough. The one-state MDP above is the step that turns their witness into a pair for $\Pi_{\mathcal{C}} \mathcal{T}^\pi$; it needs $\gamma > 2^{1/p - 1}$, and $\gamma = 0$ would make the operator constant. A remark derived here and not part of the statement: with inputs $\delta_0$ and $\delta_h$, a reward at the midpoint of the grid cell and $h \to 0$, the ratio of output to input distance is unbounded for every $\gamma \in (0,1)$. For $p = 1$ the source's remark that contractivity in $\bar d_1$ is maintained is not proved there and is not stated here.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.1, Lemma 2, proved in Appendix C.
