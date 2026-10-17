---
article_id: af_e9ce6efa24b393cd70eafabf
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.pentagonal_number_theorem
---

# Pentagonal number theorem

Euler's recurrence from the pentagonal number theorem: for `n ≥ 1`,
`p(n)` equals the finite alternating sum over nonzero `k` of
`(-1) ^ (k + 1) * p (n - g k)`, where `g k` are the generalized
pentagonal numbers. Stable source:
https://en.wikipedia.org/wiki/Pentagonal_number_theorem
("Pentagonal number theorem", statement `pentagonal-s1`).

## Depends on

- [Partition Function](partition-function.md)

## Proof depends on

- [Mk partition Function mul pentagonal Series](mk-partition-function-mul-pentagonal-ser.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.PentagonalNumber](../../../../../../../sources/v2/MathlibExt.md)
