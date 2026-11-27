# Bias of the Good–Turing estimate of the missing mass

Draw an i.i.d. sample of size $N \ge 1$ from a distribution $(p_s)$ on a countable set of species, let $n_r(N)$ be the number of species seen exactly $r$ times, and let $M_0(N) = \sum_s p_s \mathbf 1\{s \text{ unseen}\}$ be the missing mass. The Good–Turing estimate of the missing mass is $n_1(N)/N$, and its bias satisfies

$$0 \le E\Bigl[\frac{n_1(N)}{N}\Bigr] - E[M_0(N)] = \sum_s p_s^2 (1 - p_s)^{N-1} \le \frac1N$$

(Rajaraman, Thangaraj and Suresh 2017, equation (2), citing McAllester and Schapire). Indeed $E[M_0(N)] = \sum_s p_s(1 - p_s)^N$ and $E[n_1(N)] = N\sum_s p_s(1 - p_s)^{N-1}$, so the difference is $\sum_s p_s \cdot p_s(1 - p_s)^{N-1} \le \max_{0 \le p \le 1} p(1 - p)^{N-1} \le 1/N$. The exact identities $E[M_0(N)] = E[n_1(N + 1)]/(N + 1)$ and their analogues for species seen $r$ times are [the Good–Turing identity for the missing mass](../../../Biology/not-yet-classified/good-turing/expect-missing-mass.md) and [the Good–Turing identity for species seen $r$ times](../../../Biology/not-yet-classified/good-turing/expect-mass-seen.md).

## Expansion

1. The expectations of $M_0(N)$ and $n_1(N)$ as sums over species.
2. The bound $\max_{0 \le p \le 1} p(1 - p)^{N-1} \le 1/N$ and the resulting two-sided bias bound.
3. The smoothed Good–Turing estimates $(r+1)S(n_{r+1})/(N\,S(n_r))$ for the probability of each species seen $r$ times, as a separate statement.

## Sources

- N. Rajaraman, A. Thangaraj and A. T. Suresh, Minimax risk for missing mass estimation, 2017, Section I. <https://arxiv.org/abs/1705.05006>
- Good–Turing frequency estimation, Wikipedia. <https://en.wikipedia.org/wiki/Good%E2%80%93Turing_frequency_estimation>
- Original result: I. J. Good, The population frequencies of species and the estimation of population parameters, Biometrika 40 (1953), 237–264. <https://doi.org/10.1093/biomet/40.3-4.237> The estimator for the missing mass and for species seen r times follows Wikipedia and Rajaraman, Thangaraj and Suresh (2017).
