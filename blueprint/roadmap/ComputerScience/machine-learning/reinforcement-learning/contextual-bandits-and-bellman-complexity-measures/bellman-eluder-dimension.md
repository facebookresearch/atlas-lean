# Bellman eluder dimension

For an episodic MDP of horizon $H$, a value-function class $\mathcal{F}$ and the Bellman operators $\mathcal{T}_h$, the Bellman residual functions at level $h$ are $(I - \mathcal{T}_h)\mathcal{F} = \{(x,a) \mapsto f_h(x,a) - (\mathcal{T}_h f_{h+1})(x,a) : f \in \mathcal{F}\}$. Given a family $\Pi_h$ of distributions over $\mathcal{X} \times \mathcal{A}$, the **distributional eluder dimension** of a function class $\mathcal{G}$ is defined like the eluder dimension with actions replaced by distributions and $f(a)$ replaced by $\mathbb{E}_\mu[g]$. The **Bellman eluder (BE) dimension** is

$$
\dim_{\mathrm{BE}}(\mathcal{F}, \Pi, \varepsilon) = \max_{h \le H} \dim_{\mathrm{DE}}\big((I - \mathcal{T}_h)\mathcal{F}, \Pi_h, \varepsilon\big),
$$

taken with $\Pi_h$ either the roll-in distributions of greedy policies of $\mathcal{F}$ or the point masses on state-action pairs.

## Depends on

- [Eluder dimension](eluder-dimension.md)
- [Contextual decision processes and Bellman rank](bellman-rank.md)

## Sources

- C. Jin, Q. Liu, S. Miryoosefi, "Bellman Eluder Dimension: New Rich Classes of RL Problems, and Sample-Efficient Algorithms", NeurIPS (2021), arXiv:2102.00815, Definitions 6, 7 and 8.
