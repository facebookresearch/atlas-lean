---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Combinatorics.Enumerative.PermutationFixedPointIdentitiesWanted.sum_perm_sign_falling_fixedPoints_mul_pow
---

# Sum perm sign falling fixed Points mul pow

Pain's Theorem 2, with the paper's implicit parameter domain made
explicit: for `n ≥ 2`, `1 ≤ k`, and `k + 1 ≤ n`, the signed falling
fixed-point moment is
`(x - 1) ^ (n - k - 1) * n ! * (x + n - k - 1) / (n - k)!`.

The falling factor is written as a product over `Finset.range k`.
Together with the natural subtraction in `x ^ (fix σ - k)`, this gives
the polynomial derivative term also when `fix σ < k` (the product then
contains a zero factor).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.PermutationFixedPointIdentitiesWanted](../../../../../../sources/v2/WantedExt.md)
- Jean-Christophe Pain, "Identities for Permutations with Fixed Points", Theorem 2.
