# Kolmogorov's maximal inequality for finitely-valued variables

Let $\alpha$ be a finite nonempty set and $n \in \mathbb{N}$. For each $i < n$ let $p_i$ be a probability vector on $\alpha$ ($p_i(a) \ge 0$ and $\sum_{a \in \alpha} p_i(a) = 1$) and let $X_i : \alpha \to \mathbb{R}$ have mean zero, $\sum_{a \in \alpha} p_i(a) X_i(a) = 0$. Give $\alpha^n$ the product probability that assigns $\omega$ the weight $\prod_{i<n} p_i(\omega_i)$, so that the variables $\xi_i(\omega) = X_i(\omega_i)$ are independent with mean zero, and let $S_k = \xi_0 + \dots + \xi_k$. Then for every $\lambda > 0$, the probability that $|S_k| \ge \lambda$ for some $k < n$ is at most $\lambda^{-2} \sum_{i<n} \mathbb{E}[\xi_i^2] = \lambda^{-2} \sum_{i<n} \sum_{a \in \alpha} p_i(a) X_i(a)^2$.

## Idea

Chebyshev's inequality bounds the probability that the final sum is large by its variance divided by $\lambda^2$. Kolmogorov's inequality gives the same bound for the probability that some partial sum is large, which controls a whole path at the price of one variance. The proof splits the event according to the first index $k$ at which $|S_k| \ge \lambda$. On that event the remaining increment $S_{n-1} - S_k$ is independent of the first $k+1$ variables and has mean zero, so the cross term vanishes and $\mathbb{E}[S_{n-1}^2 ; \text{first exit at } k] \ge \lambda^2 P(\text{first exit at } k)$. Summing over $k$ and using $\mathbb{E}[S_{n-1}^2] = \sum_i \mathbb{E}[\xi_i^2]$ gives the bound. The same argument proves the inequality for arbitrary independent square-integrable mean-zero variables; it is the classical tool for almost-sure convergence of random series.

## Statements

- [Kolmogorov's maximal inequality for finitely-valued variables](kolmogorov-maximal-inequality.md)

## Sources

- A. Kolmogoroff, "Über die Summen durch den Zufall bestimmter unabhängiger Größen", *Mathematische Annalen* (1928).
