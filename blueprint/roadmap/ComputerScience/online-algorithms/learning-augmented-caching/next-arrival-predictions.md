# Next-arrival predictions for paging

In *paging with next-arrival predictions*, when page $\sigma_t$ is requested at time $t$, the oracle outputs a predicted time $h_t$ of the next request to $\sigma_t$; let $y_t$ be the true next request time ($+\infty$ if none). The *prediction error* is $\eta = \sum_t |h_t - y_t|$ (the $\ell_1$ error). With perfect predictions, evicting the page whose predicted next request is furthest in the future is Belady's optimal offline rule.

## Depends on

- [Consistency and robustness of learning-augmented online algorithms](consistency-and-robustness.md)
- [Optimality of furthest-in-future caching](../../greedy-algorithms-and-matroids/furthest-in-future-caching/furthest-in-future-min-misses.md)

## Sources

- Thodoris Lykouris, Sergei Vassilvitskii, "Competitive Caching with Machine Learned Advice", Journal of the ACM 68(4) (2021); ICML (2018), arXiv:1802.05399.
- Dhruv Rohatgi, "Near-Optimal Bounds for Online Caching with Machine Learned Advice", SODA (2020), arXiv:1910.12172.
