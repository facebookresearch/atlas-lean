# Good–Turing estimate of the missing mass

Draw an i.i.d. sample of size $N$ from a distribution $(p_s)$ on a countable set of species, let $n_r(N)$ be the number of species seen exactly $r$ times, and let $M_0(N) = \sum_s p_s \mathbf 1\{s \text{ unseen}\}$ be the missing mass. The Good–Turing estimate of the missing mass is $n_1(N)/N$, and its bias is at most $1/N$ in absolute value (Rajaraman, Thangaraj and Suresh 2017, equation (2), citing McAllester and Schapire). Exactly, $E[M_0(N)] = \sum_s p_s (1 - p_s)^N$ and $E[n_1(N+1)] = (N+1) \sum_s p_s (1 - p_s)^N$, so

$$E[M_0(N)] = \frac{E[n_1(N+1)]}{N+1},$$

and the bias is $E[n_1(N)/N] - E[M_0(N)] = \sum_s p_s^2 (1 - p_s)^{N-1} \in [0, 1/N]$, since $\sum_s p_s \cdot p_s(1 - p_s)^{N-1} \le \max_p p(1 - p)^{N-1} \le 1/N$. More generally the expected total mass of species seen $r$ times is $\binom{N}{r}\sum_s p_s^{r+1}(1 - p_s)^{N-r} = \frac{r+1}{N+1} E[n_{r+1}(N+1)]$, which underlies the Good–Turing estimate $(r+1) S(n_{r+1})/(N\, S(n_r))$ for the probability of each species seen $r$ times, with $S(\cdot)$ a smoothed frequency (Good–Turing frequency estimation, Wikipedia).

## Expansion

1. The model: i.i.d. sampling from a countable distribution, frequency counts and the missing mass.
2. The exact expectations of $M_0(N)$ and $n_1$, and the identity with sample size $N + 1$.
3. The bias identity and the bound $1/N$.
4. The mass of species seen $r$ times, Good's estimator, and the smoothing of the counts, kept separate.
5. The worst-case risk of the Good–Turing estimator under squared loss and concentration of the missing mass, as separate statements.

## Sources

- N. Rajaraman, A. Thangaraj and A. T. Suresh, Minimax risk for missing mass estimation, 2017, Section I. <https://arxiv.org/abs/1705.05006>
- Good–Turing frequency estimation, Wikipedia. <https://en.wikipedia.org/wiki/Good%E2%80%93Turing_frequency_estimation>
- Original result: I. J. Good, The population frequencies of species and the estimation of population parameters, Biometrika 40 (1953), 237–264. <https://doi.org/10.1093/biomet/40.3-4.237> The estimator for the missing mass and for species seen r times follows Wikipedia and Rajaraman, Thangaraj and Suresh (2017).
