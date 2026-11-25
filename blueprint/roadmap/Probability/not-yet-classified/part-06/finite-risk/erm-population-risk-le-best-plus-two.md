# Finite validation ERM is within 2ε of the best candidate

Let $\mu$ be a probability measure on $Z$, $f_1, \dots, f_M$ ($M \ge 1$) real functions on $Z$, $S = (S_1, \dots, S_n)$ a sample and $\varepsilon \in \mathbb{R}$. If for every $j$

$$\Big|\frac{1}{n} \sum_i f_j(S_i) - \int f_j \, d\mu\Big| < \varepsilon,$$

then the empirical risk minimizer $\hat\jmath$ (with a fixed tie-break) satisfies $\int f_{\hat\jmath} \, d\mu \le \min_j \int f_j \, d\mu + 2\varepsilon$.
