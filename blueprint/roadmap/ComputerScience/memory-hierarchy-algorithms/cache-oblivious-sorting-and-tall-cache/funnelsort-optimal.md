# Funnelsort is cache-obliviously optimal under a tall cache

Under the tall-cache assumption $Z = \Omega(L^2)$, funnelsort sorts $N$ elements with $O(N \log N)$ work and $O\!\left(1 + \frac{N}{L}\left(1 + \log_Z N\right)\right)$ cache misses, which equals the external-memory sorting bound $\Theta\!\left(\frac{N}{L}\log_{Z/L}\frac{N}{L}\right)$ for $N \ge Z$, simultaneously for all cache parameters.

## Proof sketch

The recurrence $Q(N) = N^{1/3} Q(N^{2/3}) + Q_{\mathrm{merge}}(N^{1/3})$, with the merger cost $O(N^{1/3} + \frac{N}{L}\log_Z N)$ from the $k$-merger lemma and base case $Q(N) = O(N/L)$ once $N = O(Z)$, solves to $O(\frac{N}{L}\log_Z N)$. Under $Z = \Omega(L^2)$, $\log_Z N = \Theta(\log_{Z/L} N)$, and comparison with the Aggarwal–Vitter bound shows optimality.

## Depends on

- [Funnelsort](funnelsort.md)
- [Space and cache complexity of a k-merger](k-merger-cost.md)
- [Aggarwal–Vitter bound for external sorting](external-sorting-bound.md)

## Proof depends on

- [Funnelsort](funnelsort.md)
- [Space and cache complexity of a k-merger](k-merger-cost.md)
- [Aggarwal–Vitter bound for external sorting](external-sorting-bound.md)

## Sources

- Matteo Frigo, Charles E. Leiserson, Harald Prokop, Sridhar Ramachandran, "Cache-Oblivious Algorithms", FOCS (1999); ACM Transactions on Algorithms 8(1) (2012).
