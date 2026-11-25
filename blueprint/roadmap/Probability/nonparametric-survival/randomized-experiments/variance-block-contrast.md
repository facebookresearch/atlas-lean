# Variance of the block-weighted difference in means

Let $U$ be a finite population of $N$ units with potential outcomes $y_{0i}, y_{1i} \in \mathbb{R}$, let $B_1, \dots, B_m \subseteq U$ be blocks and $n_1, \dots, n_m \in \mathbb{N}$. Under block randomization the treated sets $S_b \subseteq B_b$ are drawn independently, $S_b$ by complete randomization of $n_b$ treated units within $B_b$. Write $\hat\tau_b(S_b)$ for the difference in means within block $b$ (treated mean of $y_1$ over $S_b$ minus control mean of $y_0$ over $B_b \setminus S_b$), and $\hat\tau_{\mathrm{blk}} = \frac1N \sum_{b} |B_b|\, \hat\tau_b(S_b)$ for the block-weighted contrast. For each block write $S_{1,b}^2$, $S_{0,b}^2$, $S_{\tau,b}^2$ for the population variances over $B_b$ (divisor $|B_b| - 1$) of $y_1$, $y_0$ and $y_1 - y_0$. If $1 \le n_b$ and $n_b + 1 \le |B_b|$ for every $b$, then

$$\operatorname{Var}\big(\hat\tau_{\mathrm{blk}}\big) = \sum_{b=1}^m \Big(\frac{|B_b|}{N}\Big)^2 \Big(\frac{S_{1,b}^2}{n_b} + \frac{S_{0,b}^2}{|B_b| - n_b} - \frac{S_{\tau,b}^2}{|B_b|}\Big).$$

No disjointness or covering assumption on the blocks is needed.
