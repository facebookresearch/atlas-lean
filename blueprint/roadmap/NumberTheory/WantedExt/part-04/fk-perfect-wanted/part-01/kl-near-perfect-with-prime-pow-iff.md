---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.FkPerfectWanted.klNearPerfectWith_prime_pow_iff
---

# Theorem 4

**Theorem 4** (corrected): `p^a` is
`[k,ℓ]`-near-perfect with divisor `d` if and only if
`2 ≤ a ≤ k`, `d = 1`, and
`ℓ = p^{k-a} (1 + p^k + ⋯ + p^{(a-2)k})` (for `k, ℓ ≥ 1`).
The printed conclusion `a = k` is false: at `p = 2`,
`a = 2`, `k = 3`, `ℓ = 2`, `d = 1` one has
`σ₃(4) = 73 = 4³ + 1³ + 2·4` with `a ≠ k`; the printed
form is the case `a = k` of the identity
`∑_{i=1}^{a-1} p^{ik} = ℓ p^a`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.FkPerfectWanted](../../../../../../sources/v2/WantedExt.md)
- Flora Jeba S, Anirban Roy, Pankaj Jyoti Mahanta, and Manjil P. Saikia, "On Near `F_k`-Perfect and Deficient `F_k`-Perfect Numbers", Theorem 4.
