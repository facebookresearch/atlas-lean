# Fréchet-type limit of the slowest first passage times under power-law decay

Let $T_{N-k,N}$ be the $(k+1)$-st slowest of $N$ independent copies of a first passage time $\tau > 0$, and suppose its survival probability decays like a power law: $\mathbb P(\tau > t) \sim (\lambda t)^{-p}$ as $t \to \infty$, for some $\lambda > 0$ and $p > 0$.

1. **Distribution.** For each fixed integer $k \ge 0$,

$$\frac{\lambda T_{N-k,N}}{N^{1/p}} \xrightarrow{d} Z_k, \qquad \mathbb P(Z_k \le z) = \frac{\Gamma(k+1, z^{-p})}{k!} \ (z > 0), \quad \mathbb P(Z_k \le z) = 0 \ (z \le 0),$$

with $Z_k \overset{d}{=} (E_1 + \dots + E_{k+1})^{-1/p}$ for independent unit-rate exponentials $E_i$. For $k = 0$ the limit is Fréchet with shape $p$, $\mathbb P(Z_0 \le z) = \exp(-z^{-p})$. The vector $N^{-1/p}\lambda\,(T_{N-k,N}, \dots, T_{N,N})$ converges jointly to $\bigl((E_1 + \dots + E_{k+1})^{-1/p}, \dots, E_1^{-1/p}\bigr)$.

2. **Moments.** $\mathbb E[T_{N-k,N}^m] = \infty$ whenever $m \ge (k+1)p$, while for $0 < m < (k+1)p$,

$$\mathbb E\bigl[T_{N-k,N}^m\bigr] \sim \lambda^{-m} N^{m/p}\, \frac{\Gamma(k + 1 - m/p)}{\Gamma(k+1)} \qquad (N \to \infty).$$

Consequently, if $p \le 1 < (k+1)p \le Np$, then $\mathbb E[\tau] = \infty$ but $\mathbb E[T_{N-k,N}] < \infty$: for $p = 1$ each searcher has infinite mean first passage time, yet the second slowest of $N \ge 2$ searchers has finite mean.

## Expansion

At $t = N^{1/p} z/\lambda$ the expected number of unfinished searchers is $N\,\mathbb P(\tau > t) \to z^{-p}$, so the Poisson limit gives part 1 exactly as in the exponential case. Finiteness of moments follows from the exact law: $\mathbb P(T_{N-k,N} > t)$ behaves like $\binom{N}{k+1}\mathbb P(\tau > t)^{k+1} \asymp t^{-(k+1)p}$. Part 2 follows from uniform integrability of $(\lambda T_{N-k,N} N^{-1/p})^r$ for even $r$ below the threshold, with $\mathbb E[Z_k^m] = \Gamma(k+1-m/p)/\Gamma(k+1)$ from the Gamma law of $E_1 + \dots + E_{k+1}$.

## Sources

- S. D. Lawley and J. Johnson, *Slowest first passage times, redundancy, and menopause timing*, J. Math. Biol. (2023), <https://doi.org/10.1007/s00285-023-01921-9>; arXiv:2206.09255. Theorems 5 and 6; equation (21).
