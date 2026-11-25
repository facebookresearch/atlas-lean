# Block-weighted Neyman variance estimator

Let $U$ be a finite population of $N$ units with potential outcomes $y_{0i}, y_{1i}$ and blocks $B_1, \dots, B_m \subseteq U$. For treated sets $S_b \subseteq B_b$ let $\hat V_b(S_b) = s_1^2(S_b)/|S_b| + s_0^2(B_b \setminus S_b)/|B_b \setminus S_b|$ be Neyman's variance estimator within block $b$ (sample variances with divisor size minus one, $a/0 = 0$). The block-weighted Neyman estimator is

$$\hat V_{\mathrm{blk}} = \sum_{b=1}^m \Big(\frac{|B_b|}{N}\Big)^2 \hat V_b(S_b).$$
