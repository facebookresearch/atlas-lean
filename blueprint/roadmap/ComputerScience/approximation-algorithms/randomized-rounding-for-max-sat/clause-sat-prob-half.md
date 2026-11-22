# Johnson's random assignment

Setting every variable true independently with probability $1/2$, a clause with $k$ literals on
distinct variables is satisfied with [probability](clause-sat-prob.md) $1 - 2^{-k}$. This is the analysis of Johnson's algorithm
that Goemans and Williamson recall in §2: it is good for long clauses and poor for unit clauses.

## Sources

- M. X. Goemans and D. P. Williamson, "New 3/4-approximation algorithms for the maximum satisfiability problem", *SIAM J. Discrete Math.* 7(4) (1994), 656–666 (journal version), §2.
