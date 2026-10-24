---
article_id: af_d10705da73e437ad3a582d78
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Nat.kGeneralizedLucas_recurrence
---

# K Generalized Lucas recurrence

Source clause: sum of the preceding `k` values for `n ≥ 2`.
The sum over the parameter's own `Fin k` of `L_{n-k+i}` enumerates
`L_{n-k}, …, L_{n-1}`, i.e. `L_{n-1} + ⋯ + L_{n-k}`.

## Depends on

- [K Generalized Lucas](k-generalized-lucas.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.GeneralizedLucas](../../../../../sources/v2/MathlibExt.md)
