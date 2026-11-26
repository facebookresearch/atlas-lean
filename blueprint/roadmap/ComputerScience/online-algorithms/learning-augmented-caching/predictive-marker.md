# The predictive marker algorithm

For paging with cache size $k$ and next-arrival predictions with error $\eta$, the *predictive marker* algorithm (the marking algorithm that, within each phase, evicts an unmarked page with the furthest predicted next arrival, switching to random eviction along chains of repeated mistakes) has competitive ratio $O\!\left(1 + \min\!\left\{\sqrt{\eta/\mathrm{OPT}},\; \log k\right\}\right)$. It is therefore $O(1)$-consistent and $O(\log k)$-robust, matching the randomized lower bound $H_k$ up to constants without predictions.

## Proof sketch

Within a phase, a marking algorithm suffers a miss on a page evicted by mistake only if the predicted order of the next arrivals disagrees with the true order; the ranking errors are related to $\eta$ through an inversion-counting argument, and the square-root arises because many small ranking errors are needed to produce long eviction chains. Switching to uniformly random eviction after $\Theta(\log k)$ consecutive mistakes in a chain caps the phase cost at the $O(\log k)$ of the random marking algorithm.

## Depends on

- [Next-arrival predictions for paging](next-arrival-predictions.md)
- [The randomized marking algorithm and the harmonic lower bound for paging](../competitive-paging/randomized-marking-algorithm-and-the-harmonic-lower-bound.md)

## Proof depends on

- [Next-arrival predictions for paging](next-arrival-predictions.md)
- [The randomized marking algorithm and the harmonic lower bound for paging](../competitive-paging/randomized-marking-algorithm-and-the-harmonic-lower-bound.md)

## Sources

- Thodoris Lykouris, Sergei Vassilvitskii, "Competitive Caching with Machine Learned Advice", Journal of the ACM 68(4) (2021); ICML (2018), arXiv:1802.05399.
