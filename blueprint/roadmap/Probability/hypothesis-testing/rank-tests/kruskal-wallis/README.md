# Kruskal–Wallis test

The Kruskal–Wallis test compares $g \ge 2$ groups through the joint ranks of their observations. For $N = n_1 + \dots + n_g$ observations ranked jointly, with no ties, and $\bar r_i$ the average rank in group $i$, the statistic is

$$H = \frac{12}{N(N+1)} \sum_{i=1}^g n_i \Bigl(\bar r_i - \frac{N+1}{2}\Bigr)^2 = \frac{12}{N(N+1)} \sum_{i=1}^g n_i \bar r_i^2 - 3(N+1)$$

(Kruskal–Wallis test, Wikipedia). Under the null hypothesis the ranks form a uniformly random permutation of $\{1, \dots, N\}$, which holds when the observations are i.i.d. with a continuous law, so the test is distribution-free.

## Expansion

1. The model: i.i.d. continuous observations, joint ranks, and the two forms of $H$.
2. Distribution-freeness: under i.i.d. continuous sampling the rank vector is uniform on permutations and ties have probability $0$, so the law of $H$ depends only on $(n_1, \dots, n_g)$.
3. The moments of a rank sum $R_i = n_i \bar r_i$ under sampling without replacement, $E[R_i] = n_i(N+1)/2$ and $\operatorname{Var}(R_i) = n_i(N - n_i)(N+1)/12$, and the exact null mean $E[H] = g - 1$.
4. The exact null variance of $H$ and the correction for ties.
5. The chi-squared limit of the null law of $H$ with $g - 1$ degrees of freedom as $\min_i n_i \to \infty$.

## Sources

- Kruskal–Wallis test, Wikipedia, sections on the method and on the null distribution. <https://en.wikipedia.org/wiki/Kruskal%E2%80%93Wallis_test>
- Original result: W. H. Kruskal and W. A. Wallis, Use of ranks in one-criterion variance analysis, J. Amer. Statist. Assoc. 47 (1952), 583–621. <https://doi.org/10.1080/01621459.1952.10483441> The statistic and its chi-squared approximation follow Kruskal–Wallis test, Wikipedia.
