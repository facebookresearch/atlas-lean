# Distributional Bellman and categorical operators are monotone for stochastic dominance

If one return-distribution function stochastically dominates another componentwise, then so do their distributional Bellman updates and their categorical projections.

For Borel probability measures on $\mathbb{R}$ write $\nu \preceq \nu'$ when $\nu'$ [first-order stochastically dominates](../../../../../Probability/correlation-inequalities/first-order-stochastic-domination/first-order-stochastic-domination.md) $\nu$. On the real line this holds exactly when $F_\nu(t) \ge F_{\nu'}(t)$ for every $t$. For return-distribution functions write $\eta \preceq \mu$ when $\eta^{(x,a)} \preceq \mu^{(x,a)}$ for every $(x,a)$ (element-wise stochastic dominance). Let $\mathsf{p}$ be a reward–transition kernel, $\gamma \in [0,1)$, $\pi$ a stochastic policy, $\mathcal{T}^\pi$ the [distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md) and $\Pi_{\mathcal{C}}$ the [categorical projection](../categorical-distributional-reinforcement-learning/categorical-projection.md) onto a grid $z_1 < \dots < z_K$, $K \ge 2$. Then $\eta \preceq \mu$ implies

$$\mathcal{T}^\pi \eta \preceq \mathcal{T}^\pi \mu, \qquad \Pi_{\mathcal{C}} \eta \preceq \Pi_{\mathcal{C}} \mu, \qquad \Pi_{\mathcal{C}} \mathcal{T}^\pi \eta \preceq \Pi_{\mathcal{C}} \mathcal{T}^\pi \mu.$$

## Depends on

- [First-order stochastic domination](../../../../../Probability/correlation-inequalities/first-order-stochastic-domination/first-order-stochastic-domination.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)

## Proof depends on

- [First-order stochastic domination](../../../../../Probability/correlation-inequalities/first-order-stochastic-domination/first-order-stochastic-domination.md)
- [Distributional Bellman operator](../return-distributions-and-policy-evaluation/distributional-bellman-operator.md)
- [Categorical projection onto a fixed grid](../categorical-distributional-reinforcement-learning/categorical-projection.md)

## Expansion

**Distribution-function form.** The nonempty proper upper sets of $\mathbb{R}$ are the rays $(c, \infty)$ and $[c, \infty)$. Domination on $(c, \infty)$ is $1 - F_\nu(c) \le 1 - F_{\nu'}(c)$, and $[c, \infty) = \bigcap_n (c - 1/n, \infty)$ follows by continuity of measures. Rowland and coauthors define dominance by a coupling and print its support condition with the inequality reversed; the distribution-function form they give is the one used here.

**Monotonicity.** For $\gamma > 0$, $F_{(\mathcal{T}^\pi \eta)^{(x,a)}}(y) = \sum_{x',a'} \pi(a' \mid x') \int F_{\eta^{(x',a')}}((y - r)/\gamma) \, \mathsf{p}(dr, x' \mid x,a)$, which is pointwise monotone in the distribution functions of $\eta$. For $\gamma = 0$ both images are the reward marginal. The projection's distribution function is $0$ below $z_1$, $1$ from $z_K$ on, and a cell average of $F_\nu$ in between, which is again monotone. The composition is monotone. Mixtures preserve the order as well: $\nu_1 \preceq \nu_1'$ and $\nu_2 \preceq \nu_2'$ give $\lambda \nu_1 + (1 - \lambda) \nu_2 \preceq \lambda \nu_1' + (1 - \lambda) \nu_2'$ for $\lambda \in [0,1]$.

## Sources

- M. Rowland, M. G. Bellemare, W. Dabney, R. Munos and Y. W. Teh, *An Analysis of Categorical Distributional Reinforcement Learning*, Proceedings of the 21st International Conference on Artificial Intelligence and Statistics (AISTATS 2018); numbers from arXiv:1802.08163v1, <https://arxiv.org/abs/1802.08163v1>: Section 4.3, Definition 4 and Proposition 5, proved in appendix Section 9.
