---
article_id: af_502adccf8a3df9fd1bf3dcf6
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.legendreStirlingFirst_succ
---

# Legendre Stirling First succ

Triangular recurrence adjoining the next product factor:
`J(n + 1, k + 1; 1) = J(n, k; 1) - n * (n + 1) * J(n, k + 1; 1)`.
Concept `jis_sem_f66a64ccd0402d409b050315` (statements
`jis_01122ed9cc65cc42cecf4da1`, `jis_073a5750ee8a25ebbba42d0c`).

## Depends on

- [Legendre Stirling First](legendre-stirling-first.md)

## Proof depends on

- [Jacobi Stirling First](../jacobi-stirling-first-kind/jacobi-stirling-first.md)
- [Jacobi Stirling First recurrence](../jacobi-stirling-first-kind/jacobi-stirling-first-recurrence.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.LegendreStirlingFirstKind](../../../../../../../sources/v2/MathlibExt.md)
