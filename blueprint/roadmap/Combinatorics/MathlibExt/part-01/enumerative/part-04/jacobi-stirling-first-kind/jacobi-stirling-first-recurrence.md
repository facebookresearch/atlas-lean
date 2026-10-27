---
article_id: af_e5dbcabf6dfe126fea4b681a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.jacobiStirlingFirst_recurrence
---

# Jacobi Stirling First recurrence

Triangular recurrence:
`J(n+1,k+1;ζ) = J(n,k;ζ) - n * (n + ζ) * J(n,k+1;ζ)`.
Concept `jis_sem_108a092cfddb7cc6b11d221e`, from `e:JacobiStirling1` with factor
`X - n * (n + ζ)`.

## Depends on

- [Jacobi Stirling First](jacobi-stirling-first.md)

## Proof depends on

- [Jacobi Stirling First Poly](jacobi-stirling-first-poly.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.JacobiStirlingFirstKind](../../../../../../../sources/v2/MathlibExt.md)
