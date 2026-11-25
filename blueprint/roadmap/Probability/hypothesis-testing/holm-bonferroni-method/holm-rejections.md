# Hypotheses rejected by Holm's step-down procedure

Let $m \in \mathbb{N}$, $\alpha \in \mathbb{R}$, $p_0, \dots, p_{m-1} \in \mathbb{R}$ and $r$ [Holm's step-down count](holm-index.md) at level $\alpha$. Holm's procedure rejects the hypotheses whose p-value is at most $\alpha/(m - r + 1)$:

$$R = \Big\{i : p_i \le \frac{\alpha}{m - r + 1}\Big\}.$$

For $\alpha \ge 0$ these are the hypotheses with the $r$ smallest p-values ([number of rejections](card-holm-rejections.md)).
