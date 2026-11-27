# Block-weighted difference in means

Let $U$ be a finite population of $N$ units with potential outcomes $y_{0i}, y_{1i} \in \mathbb{R}$ and let $B_1, \dots, B_m \subseteq U$ be blocks. For treated sets $S_b \subseteq B_b$ write $\hat\tau_b(S_b) = \frac{1}{|S_b|}\sum_{i \in S_b} y_{1i} - \frac{1}{|B_b \setminus S_b|}\sum_{i \in B_b \setminus S_b} y_{0i}$ (with $a/0 = 0$) for the within-block difference in means. The block-weighted contrast is

$$\hat\tau_{\mathrm{blk}} = \frac{1}{N} \sum_{b=1}^{m} |B_b|\, \hat\tau_b(S_b).$$
