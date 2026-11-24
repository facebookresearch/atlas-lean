# Storey’s estimator is nonnegative

For p-values $p_1, \dots, p_m$, a level $q$ and a tuning parameter $\lambda$, let $\hat\pi_0 = (\#\{j : p_j > \lambda\} + 1)/((1 - \lambda)m)$ be Storey's estimator, $t_k = \min(\lambda, qk/(m\hat\pi_0))$ the Storey-BH thresholds, $\hat k$ the largest $k \le m$ with at least $k$ p-values at most $t_k$, and $R$ the Storey-BH rejection set $\{i : p_i \le t_{\hat k}\}$. If $\lambda \le 1$, then $\hat\pi_0 \ge 0$.
