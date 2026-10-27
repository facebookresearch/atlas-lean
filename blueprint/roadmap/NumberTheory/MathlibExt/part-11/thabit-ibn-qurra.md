---
article_id: af_1c33301f17eb55bd5d278388
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.thabit_ibn_qurra
---

# Thabit Ibn Qurra

Thabit ibn Qurra's theorem (statement thabit-s1): for `n ≥ 2` with
`p = 3 * 2 ^ n - 1`, `q = 3 * 2 ^ (n - 1) - 1`, `r = 9 * 2 ^ (2 * n - 1) - 1`
all prime, `2 ^ n * p * q` and `2 ^ n * r` are distinct amicable numbers.

Proof: Following Thabit ibn Qurra's construction as recorded in Dickson, *History of the Theory
of Numbers*, Vol. I, Ch. I, p. 39, and the cited Wikipedia account, compute full divisor sums by
multiplicativity and recover the proper-divisor sums by subtracting each number.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.ThabitIbnQurra](../../../../sources/v2/MathlibExt.md)
- https://en.wikipedia.org/wiki/Amicable_numbers#Th%C4%81bit_ibn_Qurra_theorem
