# The marking algorithm is H_k-competitive on k+1 pages

If all requests and the initial cache lie in a set of at most $k + 1$ pages, then each phase of the randomized marking algorithm contains at most one clean request, the number of clean requests is at most the optimal offline cost, and the marking algorithm is $(H_k, 0)$-competitive against an oblivious adversary, where $H_k = 1 + \frac12 + \dots + \frac1k$. This matches the $H_k$ lower bound for randomized paging. On more pages the bound $2 H_k$ cannot be improved to $H_k$ in general: already for $k = 2$ on four pages, repeating the requests $2, 3, 0, 1, 3, 2, 1, 0$ from the cache $\{0, 1\}$ forces expected cost $8m$ against offline cost $4m + 1$, so marking is not $(c, b)$-competitive for any $c < 2$.

## Proof sketch

With $k+1$ pages a phase has exactly one new page, and the offline algorithm must fault once per phase. Within a phase, the $i$-th request to a stale page finds it evicted with probability at most $1/(k - i + 1)$ because the unmarked pages in cache are uniformly distributed, and summing gives at most $H_k$ expected faults per phase.

## Depends on

- [The randomized marking algorithm and the harmonic lower bound for paging](../competitive-paging/randomized-marking-algorithm-and-the-harmonic-lower-bound.md)
- [Randomized online strategies against an oblivious adversary](../competitive-analysis/randomized-online-strategies.md)

## Proof depends on

- [The randomized marking algorithm and the harmonic lower bound for paging](../competitive-paging/randomized-marking-algorithm-and-the-harmonic-lower-bound.md)

## Sources

- A. Fiat, R. M. Karp, M. Luby, L. A. McGeoch, D. D. Sleator and N. E. Young, "Competitive Paging Algorithms", Journal of Algorithms 12(4), 1991; arXiv:cs/0205038.
