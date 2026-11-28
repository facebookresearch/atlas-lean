# Bellman eluder dimension

For an episodic MDP of horizon $H$, a value-function class $\mathcal{F}$ and the Bellman operators $\mathcal{T}_h$, the Bellman residual functions at level $h$ are $(I - \mathcal{T}_h)\mathcal{F} = \{(x,a) \mapsto f_h(x,a) - (\mathcal{T}_h f_{h+1})(x,a) : f \in \mathcal{F}\}$. Given a family $\Pi_h$ of distributions over $\mathcal{X} \times \mathcal{A}$, a distribution $\nu$ is **$\varepsilon$-independent** of distributions $\mu_1, \dots, \mu_n$ with respect to a function class $\mathcal{G}$ if a single $g \in \mathcal{G}$ satisfies $\sqrt{\sum_{i=1}^n (\mathbb{E}_{\mu_i}[g])^2} \le \varepsilon$ but $|\mathbb{E}_\nu[g]| > \varepsilon$. The **distributional eluder dimension** $\dim_{\mathrm{DE}}(\mathcal{G}, \Pi_h, \varepsilon)$ is the length of the longest sequence $\rho_1, \dots, \rho_n \in \Pi_h$ for which there is $\varepsilon' \ge \varepsilon$ such that every $\rho_i$ is $\varepsilon'$-independent of $\rho_1, \dots, \rho_{i-1}$. The **Bellman eluder (BE) dimension** is

$$
\dim_{\mathrm{BE}}(\mathcal{F}, \Pi, \varepsilon) = \max_{h \le H} \dim_{\mathrm{DE}}\big((I - \mathcal{T}_h)\mathcal{F}, \Pi_h, \varepsilon\big),
$$

taken with $\Pi_h$ either the roll-in distributions of greedy policies of $\mathcal{F}$ or the point masses on state-action pairs.

## Depends on

- [Eluder dimension](eluder-dimension.md)
- [Contextual decision processes and Bellman rank](bellman-rank.md)

## Sources

- C. Jin, Q. Liu, S. Miryoosefi, "Bellman Eluder Dimension: New Rich Classes of RL Problems, and Sample-Efficient Algorithms", NeurIPS (2021), arXiv:2102.00815, Definitions 6, 7 and 8.
