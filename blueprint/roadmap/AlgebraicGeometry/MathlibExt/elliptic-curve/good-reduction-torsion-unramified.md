---
article_id: af_a89d38262f4f8ce3249c2e31
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.good_reduction_torsion_unramified
---

# Neron Ogg Shafarevich

The easy direction of the **Néron–Ogg–Shafarevich criterion**: if `E`
over `Frac R` has good reduction at the discrete valuation ring `R`, then every
element of the inertia subgroup fixes every `n`-torsion point of `E` over the
separable closure, where `n` is nonzero in the residue field.

Note: upstream states torsion membership via `AddSubgroup.torsionBy`, which is
absent from Mathlib; here it is unfolded to the membership condition
`(n : ℤ) • P = 0`, which is definitionally the same condition.

Proof: We use Silverman's elementary valuation filtration at the origin in `(z, w)` coordinates,
together with reduction to the nonsingular residue curve; see *The Arithmetic of Elliptic Curves*,
IV.1, VII.3, and VII.7.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.AlgebraicGeometry.EllipticCurve.NeronOggShafarevich](../../../../sources/v2/MathlibExt.md)
- J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer, Theorem VII.7.1.
