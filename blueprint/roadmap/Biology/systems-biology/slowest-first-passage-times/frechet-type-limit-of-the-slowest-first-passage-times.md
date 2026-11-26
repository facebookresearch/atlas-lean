# Fréchet-type limit of the slowest first passage times under power-law decay

Let $T_{N-k,N}$ be the $(k+1)$-st slowest of $N$ independent copies of a first passage time $\tau > 0$, and suppose its survival probability decays like a power law: $\mathbb P(\tau > t) \sim (\lambda t)^{-p}$ as $t \to \infty$, for some $\lambda > 0$ and $p > 0$.

1. **Distribution.** For each fixed integer $k \ge 0$,

$$\frac{\lambda T_{N-k,N}}{N^{1/p}} \xrightarrow{d} Z_k, \qquad \mathbb P(Z_k \le z) = \frac{\Gamma(k+1, z^{-p})}{k!} \ (z > 0), \quad \mathbb P(Z_k \le z) = 0 \ (z \le 0),$$

with $Z_k \overset{d}{=} (E_1 + \dots + E_{k+1})^{-1/p}$ for independent unit-rate exponentials $E_i$. For $k = 0$ the limit is Fréchet with shape $p$, $\mathbb P(Z_0 \le z) = \exp(-z^{-p})$. The vector $N^{-1/p}\lambda\,(T_{N-k,N}, \dots, T_{N,N})$ converges jointly to $\bigl((E_1 + \dots + E_{k+1})^{-1/p}, \dots, E_1^{-1/p}\bigr)$.

2. **Moments.** For $N > k$, $\mathbb E[T_{N-k,N}^m] = \infty$ whenever $m \ge (k+1)p$, while for $0 < m < (k+1)p$,

$$\mathbb E\bigl[T_{N-k,N}^m\bigr] \sim \lambda^{-m} N^{m/p}\, \frac{\Gamma(k + 1 - m/p)}{\Gamma(k+1)} \qquad (N \to \infty).$$

Consequently, if $p \le 1 < (k+1)p \le Np$, then $\mathbb E[\tau] = \infty$ but $\mathbb E[T_{N-k,N}] < \infty$: for $p = 1$ each searcher has infinite mean first passage time, yet the second slowest of $N \ge 2$ searchers has finite mean.

## Proof depends on

- [Poisson limit of elementary symmetric sums of uniformly small terms](../../bioinformatics/sequence-alignment/two-sequence-karlin-altschul-statistics/tendsto-elem-symm.md)

## Expansion

At $t = N^{1/p} z/\lambda$ the expected number of unfinished searchers is $N\,\mathbb P(\tau > t) \to z^{-p}$, so the Poisson limit of the binomial count gives part 1 exactly as in the exponential case. Finiteness of moments follows from the exact law: $\mathbb P(T_{N-k,N} > t)$ behaves like $\binom{N}{k+1}\mathbb P(\tau > t)^{k+1} \asymp t^{-(k+1)p}$. For part 2 fix a real exponent $r$ with $m < r < (k+1)p$; an even integer need not exist there (for $k = 0$, $p = 1$, $m = 1/2$ even the second moment is infinite). Put $X_N = \lambda T_{N-k,N} N^{-1/p}$. Choose $t_0$ and $C$ with $\mathbb P(\tau > t) \le C(\lambda t)^{-p}$ for $t \ge t_0$. The union bound over $(k+1)$-subsets gives $\mathbb P(T_{N-k,N} > t) \le \binom{N}{k+1}\mathbb P(\tau > t)^{k+1} \le \bigl(N\,\mathbb P(\tau > t)\bigr)^{k+1}/(k+1)!$, so $\mathbb P(X_N > x) \le (Cx^{-p})^{k+1}/(k+1)!$ for all $x \ge \lambda t_0$ and all $N$. Integrating, $\sup_N \mathbb E[X_N^r] \le (\lambda t_0)^r + \int_{\lambda t_0}^\infty r x^{r-1}(Cx^{-p})^{k+1}/(k+1)!\,dx < \infty$, so $\{X_N^m\}_N$ is uniformly integrable, and the convergence in distribution of part 1 gives $\mathbb E[X_N^m] \to \mathbb E[Z_k^m] = \Gamma(k+1-m/p)/\Gamma(k+1)$, from the Gamma law of $E_1 + \dots + E_{k+1}$.

## Sources

- S. D. Lawley and J. Johnson, *Slowest first passage times, redundancy, and menopause timing*, J. Math. Biol. (2023), <https://doi.org/10.1007/s00285-023-01921-9>; arXiv:2206.09255. Numbering as in arXiv v2: Section 2.3, Theorems 5 and 6 and display (21) (journal version: Theorems 4 and 5).
