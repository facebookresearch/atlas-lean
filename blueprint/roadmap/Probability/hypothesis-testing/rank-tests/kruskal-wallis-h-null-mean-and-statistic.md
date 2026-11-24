# Kruskal–Wallis statistic: null mean and distribution-freeness

Let $N = n_1 + \dots + n_g$ observations in $g \ge 2$ groups with all $n_i \ge 1$ be ranked jointly, with no ties, and let $\bar r_i$ be the average rank in group $i$. The Kruskal–Wallis statistic is then
$$H = \frac{12}{N(N+1)} \sum_{i=1}^g n_i \Bigl(\bar r_i - \frac{N+1}{2}\Bigr)^2 = \frac{12}{N(N+1)} \sum_{i=1}^g n_i \bar r_i^2 - 3(N+1),$$
and for large groups its null distribution is approximated by the chi-squared distribution with $g - 1$ degrees of freedom, while for small groups the exact distribution should be used (Kruskal–Wallis test, Wikipedia). Under the null hypothesis that the ranks form a uniformly random permutation of $\{1, \dots, N\}$, which holds when the observations are i.i.d. with a continuous law, the law of $H$ depends only on $(n_1, \dots, n_g)$, not on the common law. Moreover, the rank sum $R_i = n_i \bar r_i$ is the total of a sample of size $n_i$ drawn without replacement from $\{1, \dots, N\}$, so $E[R_i] = n_i(N+1)/2$ and $\operatorname{Var}(R_i) = n_i(N - n_i)(N+1)/12$, and therefore
$$E[H] = \frac{12}{N(N+1)} \sum_{i=1}^g \frac{\operatorname{Var}(R_i)}{n_i} = \frac{1}{N} \sum_{i=1}^g (N - n_i) = g - 1 .$$

## Expansion

1. The model: i.i.d. continuous observations, joint ranks, and the two forms of $H$.
2. Distribution-freeness: under i.i.d. continuous sampling the rank vector is uniform on permutations and ties have probability $0$.
3. The first two moments of a rank sum under sampling without replacement, and the computation of $E[H] = g - 1$.
4. The chi-squared approximation with $g - 1$ degrees of freedom, the exact null variance of $H$, and the correction for ties, as separate statements.

## Sources

- Kruskal–Wallis test, Wikipedia, sections on the method and on the null distribution. <https://en.wikipedia.org/wiki/Kruskal%E2%80%93Wallis_test>
- Original result: W. H. Kruskal and W. A. Wallis, Use of ranks in one-criterion variance analysis, J. Amer. Statist. Assoc. 47 (1952), 583–621. <https://doi.org/10.1080/01621459.1952.10483441> The statistic and its chi-squared approximation follow Kruskal–Wallis test, Wikipedia.
