# The sampled projected categorical target is conditionally unbiased

Averaged over the sampled reward, next state and next action, the projected sampled target equals the projected distributional Bellman update. Then the sampling noise is a signed measure of total mass zero with conditional mean zero.

Let $\mathsf{p}$ be a reward–transition kernel, $\gamma \in [0,1)$, $\pi$ a stochastic policy, $\mathcal{T}^\pi$ the [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md) and $\Pi_{\mathcal{C}}$ the [categorical projection](../categorical-distributional-reinforcement-learning/categorical-projection.md) onto a grid $z_1 < \dots < z_K$, $K \ge 2$. Fix $\eta \in \mathscr{P}(\mathbb{R})^{\mathcal{X} \times \mathcal{A}}$ and $(x,a)$, draw $(R, X') \sim \mathsf{p}(\cdot \mid x,a)$ and then $A' \sim \pi(\cdot \mid X')$, and let

$$N = \Pi_{\mathcal{C}} (f_{R,\gamma})_\# \eta^{(X',A')} - (\Pi_{\mathcal{C}} \mathcal{T}^\pi \eta)^{(x,a)}.$$

Then $N$ is a random signed measure on the grid with $N(\mathbb{R}) = 0$, $|N((-\infty, y])| \le 1$, and $\mathbb{E}[N(B)] = 0$ for every Borel $B$. In the evaluation variant of the [categorical algorithm](../categorical-distributional-reinforcement-learning/categorical-evaluation-with-mixture-updates.md), with $\eta = \eta_t$ and $(x,a) = (x_t, a_t)$, this gives $\mathbb{E}[N_t((-\infty, y]) \mid \mathcal{F}_t] = 0$ almost surely for every $y$, a [conditional expectation given the σ-field](../../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md) $\mathcal{F}_t$, which contains the real-valued past rewards.

## Depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Sample-based categorical evaluation and Q-learning with mixture updates](../categorical-distributional-reinforcement-learning/categorical-evaluation-with-mixture-updates.md)
- [Conditional expectation given a σ-field](../../../../../Probability/foundations/conditional-expectation/conditional-expectation-given-a-sigma-field/conditional-expectation.md)

## Proof depends on

- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)
- [Sample-based categorical evaluation and Q-learning with mixture updates](../categorical-distributional-reinforcement-learning/categorical-evaluation-with-mixture-updates.md)

## Expansion

$\Pi_{\mathcal{C}} \nu (B) = \sum_{i : z_i \in B} \int h_i \, d\nu$ is linear in $\nu$, and the hat functions $h_i$ are bounded and measurable. So by Fubini,

$$\mathbb{E} \int h_i \, d(f_{R,\gamma})_\# \eta^{(X',A')} = \sum_{(x',a')} \pi(a' \mid x') \int \int h_i(r + \gamma w) \, \eta^{(x',a')}(dw) \, \mathsf{p}(dr, x' \mid x,a) = \int h_i \, d(\mathcal{T}^\pi \eta)^{(x,a)}.$$

Both terms of $N$ are probability measures, which gives total mass $0$ and the bound $1$ on its distribution function. In the algorithm, $\eta_t$ and $(x_t, a_t)$ are $\mathcal{F}_t$-measurable and the sampling conditions give the conditional laws of $(r_t, x_{t+1}, a^*_t)$, so the identity holds conditionally on $\mathcal{F}_t$; $N_t$ itself is $\mathcal{F}_{t+1}$-measurable, being a function of $\eta_t$, $(x_t, a_t)$ and the sample. Rowland and coauthors state this as Lemma 4 without a separate proof and use it in the proof of their Lemma 6.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.3, Lemma 4, and its use in Appendix C, proof of Lemma 6.
