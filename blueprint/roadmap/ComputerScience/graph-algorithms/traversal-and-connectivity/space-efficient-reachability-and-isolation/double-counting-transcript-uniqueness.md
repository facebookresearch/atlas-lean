# Unique double-counting transcripts characterize min-unique rounds

With exact counts $c_k$ and $\Sigma_k$, the double-counting procedure for round $k$ has exactly one passing transcript if and only if every vertex of $R_k$ has exactly one shortest walk from $s$. Consequently, on graphs in which every reachable vertex has a unique shortest walk from $s$ (min-unique graphs), the round-by-round controller is unambiguous: it has exactly one accepting computation path, which decides reachability of the target; and when some round is not unique, the controller returns the first non-unique round.

## Proof sketch

A passing transcript must supply every vertex of $R_k$ with a walk of length exactly its distance; the transcript is unique exactly when each such shortest walk is unique.

## Depends on

- [Reinhardt-Allender double counting](reinhardt-allender-double-counting.md)

## Sources

- K. Reinhardt and E. Allender, "Making Nondeterminism Unambiguous", SIAM Journal on Computing 29(4), 2000.
