# The additive fit minimizes the weighted squared error

Let $p$ be allele frequencies ($p_i \ge 0$, $\sum_i p_i = 1$) and $G$ symmetric genotypic values. Then for every real $c$ and every $a : A \to \mathbb{R}$,

$$V_D \le \sum_{i, j} p_i p_j\, (G_{ij} - c - a_i - a_j)^2,$$

where $V_D$ is the [dominance variance](dom-var.md), the weighted squared error of the additive fit $\mu + \alpha_i + \alpha_j$: no function additive over the two genes fits better (Fisher 1918).

## Sources

- R. A. Fisher, *The correlation between relatives on the supposition of Mendelian inheritance*, Trans. R. Soc. Edinb. 52 (1918), 399–433.
