---
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Algebra.PalindromicZeroOneWanted.existsUnique_evenOdd_reciprocal
---

# Lemma 2.1

**Lemma 2.1**: let `h(x) ∈ ℤ[x]` be an irreducible
reciprocal polynomial of degree `2k` which is not a
polynomial in `x^2`. Then there exist unique reciprocal
polynomials `h_e, h_o ∈ ℤ[x]` and a unique positive odd
integer `ℓ` such that `deg h_e = k`, `deg h_o = k - ℓ`,
`h(x) = h_e(x^2) + x^ℓ h_o(x^2)` and
`h_e(0) h_o(0) ≠ 0`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Algebra.PalindromicZeroOneWanted](../../../../sources/v2/WantedExt.md)
- Pradipto Banerjee and Amit Kundu, "On an Irreducibility Question Concerning Palindromic Non-cyclotomic 0,1-Polynomials", Lemma 2.1.
