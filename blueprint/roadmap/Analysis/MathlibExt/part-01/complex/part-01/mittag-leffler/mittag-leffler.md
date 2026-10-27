---
article_id: af_a00abe70c475ee99e38c123a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.MittagLefflerWanted.mittag_leffler
---

# Mittag leffler

For closed discrete `S ⊆ ℂ` and any `coeff : ↥S → ℕ →₀ ℂ`, there exists `f : ℂ → ℂ` holomorphic on
`Sᶜ` and meromorphic on `ℂ` whose difference from `principalPart s.val (coeff s)` is analytic at
each `s ∈ S`. Source: Mittag-Leffler theorem, G. Mittag-Leffler, Acta Math. 4 (1884); see Rudin;
Lean is closed discrete S with punctured-ball isolation, prescribed finite principal parts via
Finsupp, global meromorphic existence holomorphic on Sᶜ.

## Depends on

- [Principal Part](principal-part.md)

## Proof depends on

- [Mittag leffler of is Discrete](mittag-leffler-of-is-discrete.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.MittagLeffler](../../../../../../../sources/v2/MathlibExt.md)
