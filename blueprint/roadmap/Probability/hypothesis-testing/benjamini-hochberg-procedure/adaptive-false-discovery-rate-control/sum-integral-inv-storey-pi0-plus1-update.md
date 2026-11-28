# Expected inverse leave-one-out Storey estimators

Let $p_1, \dots, p_m$ be measurable p-values on a probability space, each true-null p-value valid and independent of the other p-values, $0 \le \lambda < 1$, and $\hat\pi_0^{(i)}$ the finite-sample (plus-one) [Storey estimator](storey-pi0-plus1.md) $\hat\pi_0(\lambda) = (\#\{j : p_j > \lambda\} + 1)/((1-\lambda)m)$ computed with $p_i$ replaced by $0$. Then $\sum_{i \in H_0}\mathbb{E}[1/\hat\pi_0^{(i)}] \le m$.
