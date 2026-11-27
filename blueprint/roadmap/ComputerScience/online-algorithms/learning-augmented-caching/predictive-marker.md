# The predictive marker algorithm

For paging with cache size $k$ and next-arrival predictions with $\ell_1$ error $\eta$, the *predictive marker* algorithm has competitive ratio at most

$$
2\min\left\{1 + 2\sqrt{5\,\eta/\mathrm{OPT}},\; 2H_k\right\} = O\!\left(1 + \min\left\{\sqrt{\eta/\mathrm{OPT}},\; \log k\right\}\right).
$$

It is a marking algorithm: on a miss caused by a clean page (one not requested in the previous phase) it evicts the unmarked cached page with the latest predicted next arrival; a miss caused by a stale page extends that page's eviction chain, and the algorithm keeps evicting by latest predicted arrival while the chain has length at most $H_k$ and evicts a uniformly random unmarked page afterwards. It is therefore $O(1)$-consistent and $O(\log k)$-robust, matching up to constants the randomized lower bound $H_k$ without predictions.

## Proof sketch

The evictions of a phase decompose into disjoint chains, one per clean page. A chain of length $T$ of evictions that follow the predictions requires the predicted order of next arrivals to reverse a run of $T$ true arrivals, and the $\ell_1$ error of such a reversal is at least about $T^2/5$ (the spread of the $\ell_1$ loss is at most $\sqrt{5m}$), which yields the square root. Since the optimum pays at least half the number of clean pages, summing over chains gives $2(1 + 2\sqrt{5\eta/\mathrm{OPT}})$. After a chain reaches length $H_k$ evictions are random, and an analysis of random marking shows that each chain then contributes at most $H_k$ further misses in expectation, which gives $4H_k$.

## Depends on

- [Next-arrival predictions for paging](next-arrival-predictions.md)
- [Consistency and robustness of learning-augmented online algorithms](consistency-and-robustness.md)

## Proof depends on

- [The randomized marking algorithm and the harmonic lower bound for paging](../competitive-paging/randomized-marking-algorithm-and-the-harmonic-lower-bound.md)

## Sources

- Thodoris Lykouris, Sergei Vassilvitskii, "Competitive Caching with Machine Learned Advice", Journal of the ACM 68(4) (2021); ICML (2018), arXiv:1802.05399, Algorithm 1, Lemma 3.1 and Theorem 3.3.
