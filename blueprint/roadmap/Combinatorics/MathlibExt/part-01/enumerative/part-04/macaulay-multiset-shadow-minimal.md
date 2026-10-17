---
article_id: af_7fb39375800ed5376c1f7dd1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.macaulay_multiset_shadow_minimal
---

# Macaulay Monomial Shadow

Macaulay multiset-shadow lower bound (Theorem M).

Finitely supported exponent vectors `ℕ →₀ ℕ` model monomials/multisets of a
fixed degree; the union of single-positive-exponent deletions `a.update i (a i - 1)`
over `i ∈ a.support` is the shadow. The explicit `digits i = 0` branch preserves
the empty-family convention, since natural subtraction followed by
`Nat.choose 0 0` would otherwise count a spurious term.

Proof: We formalize the binomial-cascade split inequality and coordinate-slice induction of
Ábrego, Fernández-Merchant, and Llano, their route from Theorem 1 to Theorem M.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.MacaulayMonomialShadow](../../../../../../sources/v2/MathlibExt.md)
- Bernardo M. Ábrego, Silvia Fernández-Merchant, and Bernardo Llano, "An Inequality for Macaulay Functions," Journal of Integer Sequences 14 (2011), Theorem M, lines 215–223. Source: <https://cs.uwaterloo.ca/journals/JIS/VOL14/Abrego/abrego2.tex>. Full-source SHA-256 `0a56d8b3c040a0fb5bb57262e0605376eddfdc967da9d2fd58b37f3e4bad64ed`. Theorem-span SHA-256 `4e9a68f171676aeb3dd5c8c605faa0e677f46e831861a5ccb74de985dd6ffa87`.
