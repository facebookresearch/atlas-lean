# The key equations are solvable

Let $F$ be a field, let $\alpha_0, \dots, \alpha_{n-1} \in
F$ and let $p \in F[X]$ have degree less than $k$. If a received word $y \in F^n$ differs from the
encoding $(p(\alpha_0), \dots, p(\alpha_{n-1}))$ in at most $e$ coordinates, then the
Berlekamp-Welch key equations for $y$ with parameters $k$ and $e$ have a solution $(Q, E)$.

A solution is the error locator polynomial, padded to degree $e$, together with $Q = pE$.
