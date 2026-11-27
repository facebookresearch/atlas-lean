# Realized and predictable quadratic variations agree

Let row $n$ of a triangular array $\xi$ be square-integrable, with $\xi_{n,i}$ measurable for
$\mathcal F_{n,i+1}$, and satisfy the Lindeberg condition. Let $k_n \le n$. If the predictable
quadratic variations $V_n = \sum_{j < k_n} E[\xi_{n,j}^2 \mid \mathcal F_{n,j}]$ are bounded in
probability, then
$\max_{i \le k_n} |\sum_{j < i} \xi_{n,j}^2 - \sum_{j < i} E[\xi_{n,j}^2 \mid \mathcal F_{n,j}]| \to 0$
in probability. The martingale property $E[\xi_{n,i} \mid \mathcal F_{n,i}] = 0$ is not needed.

## Sources

- P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*, Academic Press (1980), Chapter 2, on comparing the sums of squares of martingale array increments with their conditional variances.
