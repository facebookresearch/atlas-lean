# Null distribution of the Kruskal–Wallis statistic

Let the $N = n_1 + \dots + n_g$ observations of $g \ge 2$ groups, with every $n_i \ge 1$, be i.i.d. with a continuous law, so that ties have probability $0$, and let $H$ be the [Kruskal–Wallis statistic](README.md) computed from their joint ranks. Under this null model the vector of joint ranks is uniformly distributed on the permutations of $\{1, \dots, N\}$, so the law of $H$ depends only on $(n_1, \dots, n_g)$. The rank sum $R_i = n_i \bar r_i$ of group $i$ is the sum of a sample of size $n_i$ drawn without replacement from $\{1, \dots, N\}$, so $E[R_i] = n_i(N+1)/2$ and $\operatorname{Var}(R_i) = n_i(N - n_i)(N+1)/12$, and hence

$$E[H] = \frac{12}{N(N+1)} \sum_{i=1}^g \frac{\operatorname{Var}(R_i)}{n_i} = \frac{1}{N} \sum_{i=1}^g (N - n_i) = g - 1.$$

## Expansion

1. The model: i.i.d. continuous observations, joint ranks, and the two forms of $H$.
2. Distribution-freeness: under i.i.d. continuous sampling the rank vector is uniform on permutations and ties have probability $0$, so the law of $H$ depends only on $(n_1, \dots, n_g)$.
3. The moments of a rank sum $R_i = n_i \bar r_i$ under sampling without replacement, $E[R_i] = n_i(N+1)/2$ and $\operatorname{Var}(R_i) = n_i(N - n_i)(N+1)/12$, and the exact null mean $E[H] = g - 1$.
4. The exact null variance of $H$ and the correction for ties.
5. The chi-squared limit of the null law of $H$ with $g - 1$ degrees of freedom as $\min_i n_i \to \infty$.

## Sources

- Kruskal–Wallis test, Wikipedia, sections on the method and on the null distribution. <https://en.wikipedia.org/wiki/Kruskal%E2%80%93Wallis_test>
- Original result: W. H. Kruskal and W. A. Wallis, Use of ranks in one-criterion variance analysis, J. Amer. Statist. Assoc. 47 (1952), 583–621. <https://doi.org/10.1080/01621459.1952.10483441> The statistic and its chi-squared approximation follow Kruskal–Wallis test, Wikipedia.
