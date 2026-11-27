# Unbiasedness of the block-weighted difference in means

Let $U$ be a finite population of $N$ units with potential outcomes $y_{0i}, y_{1i} \in \mathbb{R}$, let $B_1, \dots, B_m \subseteq U$ be blocks and $n_1, \dots, n_m \in \mathbb{N}$. Under block randomization the treated sets $S_b \subseteq B_b$ are drawn independently, $S_b$ by complete randomization of $n_b$ treated units within $B_b$. Write $\hat\tau_b(S_b)$ for the difference in means within block $b$ (treated mean of $y_1$ over $S_b$ minus control mean of $y_0$ over $B_b \setminus S_b$), and $\hat\tau_{\mathrm{blk}} = \frac1N \sum_{b} |B_b|\, \hat\tau_b(S_b)$ for the block-weighted contrast. Suppose the blocks partition $U$ (pairwise disjoint, with union $U$) and every block has a treated and a control unit, $1 \le n_b$ and $n_b + 1 \le |B_b|$. Then

$$\mathbb{E}\big[\hat\tau_{\mathrm{blk}}\big] = \frac1N \sum_{i \in U} (y_{1i} - y_{0i}),$$

the population average treatment effect.
