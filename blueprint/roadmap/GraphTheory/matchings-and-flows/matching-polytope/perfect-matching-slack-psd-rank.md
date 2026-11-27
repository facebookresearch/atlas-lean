# Superpolynomial PSD rank of perfect-matching slack

For even $n\ge4$, take columns indexed by perfect matchings $M$ of $K_n$, and rows by either an edge $e$ or an odd-cardinality subset $U$ of vertices. In edge rows the entry is $1_{e\in M}$; in odd-cut rows it is $|M\cap\delta(U)|-1$. Define the real PSD rank to be the least positive integer $r$ with real positive semidefinite $r\times r$ factors $A_i$ for rows and $B_M$ for columns satisfying $S_{iM}=\mathrm{tr}(A_i B_M)$. For every real $C>0$ there is $n_0\ge4$ such that at every even $n\ge n_0$ the PSD rank exceeds $n^C$.

## Depends on

- Perfect-matching indicator and odd-cut slack rows, real positive semidefinite factorization and positive-order rank.

## Proof outline

Prove existence of a finite PSD factorization to justify the natural-number minimum, then lower-bound positive matrix order without equivariance assumptions. Include trivial zero odd-cut rows without changing the statement.

- Superpolynomial lower bound on arbitrary real PSD factors for the unshifted slack matrix.

## Sources

- [Comparator statement: `OAI.PerfectMatchingPSD.main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatchingPSD.lean#L50-L52)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/126.md)
