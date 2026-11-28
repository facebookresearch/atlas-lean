# Next-arrival predictions for paging

In *paging with next-arrival predictions*, a request sequence $\sigma_1, \dots, \sigma_n$ arrives online, and when page $\sigma_t$ is requested at time $t$, the oracle outputs a predicted time $h_t$ of the next request to $\sigma_t$; let $y_t$ be the true next request time, with $y_t = n + 1$ if $\sigma_t$ is not requested again. The *prediction error* is $\eta = \sum_{t=1}^{n} |h_t - y_t|$ (the $\ell_1$ error). With perfect predictions, evicting the page whose predicted next request is furthest in the future is Belady's optimal offline rule.

## Depends on

- [Consistency and robustness of learning-augmented online algorithms](consistency-and-robustness.md)
- [Deterministic online paging algorithm](../competitive-paging/deterministic-online-paging-algorithm.md)

## Sources

- Thodoris Lykouris, Sergei Vassilvitskii, "Competitive Caching with Machine Learned Advice", Journal of the ACM 68(4) (2021); ICML (2018), arXiv:1802.05399.
- Dhruv Rohatgi, "Near-Optimal Bounds for Online Caching with Machine Learned Advice", SODA (2020), arXiv:1910.12172.
