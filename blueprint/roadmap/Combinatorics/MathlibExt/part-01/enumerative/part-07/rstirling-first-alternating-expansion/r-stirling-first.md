---
article_id: af_9dc7935a6716c654ea8a8af7
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.rStirlingFirst
---

# R Stirling First

Unsigned r-Stirling number of the first kind, after A. Z. Broder,
"The r-Stirling numbers", Stanford Computer Science Report STAN-CS-82-949
(December 1982), PDF page 12 / printed page 9, Equation (24);
journal version: Discrete Mathematics 49 (1984), 241-259,
DOI 10.1016/0012-365X(84)90161-4.

Equation (24) characterizes `[n,m]_r` by
`∑ k, [n,k]_r z^k = z^r (z+r)(z+r+1)...(z+n-1)` for `n ≥ r > 0`.
The definition below is the coefficient of `X^m` in
`X^r * ∏ k in Finset.Ico r n, (X + C k)` over `Polynomial ℕ`,
which directly implements Equation (24), including zero outside the
triangular support.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.RStirlingFirstAlternatingExpansion](../../../../../../../sources/v2/MathlibExt.md)
