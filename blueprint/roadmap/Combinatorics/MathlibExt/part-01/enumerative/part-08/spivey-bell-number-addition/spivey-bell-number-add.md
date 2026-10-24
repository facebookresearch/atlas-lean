---
article_id: af_f1bd85feb2c73f59415d4569
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.spivey_bell_number_add
---

# Spivey bell number add

Spivey's Bell-number addition formula: `(n + m).bell` equals the double
sum over `j = 0..m` and `k = 0..n` of
`j ^ (n - k) * S(m, j) * C(n, k) * B_k`, with natural subtraction and power
(`0 ^ 0 = 1`).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.SpiveyBellNumberAddition](../../../../../../../sources/v2/MathlibExt.md)
- Michael Z. Spivey, *A Generalized Recurrence for Bell Numbers*, Journal of Integer Sequences 11 (2008), Article 08.2.5, equation `Bell_Gen`, lines 113–117, <https://cs.uwaterloo.ca/journals/JIS/VOL11/Spivey/spivey25.tex>.
