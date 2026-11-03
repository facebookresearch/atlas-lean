/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Statement.Definitions
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Surjection dimension bound
For `S = coneQuotient n K G` and any ideal `P` of
`R = MvPolynomial (Fin (n + 2)) K` containing the system
(`Ideal.span (Set.range G) ≤ P`), Krull dimension can only drop along the
surjection `S ↠ R ⧸ P`: `Ring.KrullDimLE 1 (R ⧸ P)` follows from
`hZd : IsZeroDimensional n K G` (which is `Ring.KrullDimLE 1 S`).

Naming quirk: despite the name, `IsZeroDimensional` bounds the cone by `1`,
not `0` — `S` is the affine cone over the (zero-dimensional) projective
locus, so `Ring.KrullDimLE 1 S` is the correct reading.

This is stated in the exact `Ring.KrullDimLE` shape chunk B4
(`HeightLowerBound.lean`) consumes directly with `hZd`.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- Dimension drops along the cone-to-quotient surjection: if `P` contains the
system `G`, then `R ⧸ P` is a quotient of the cone `S`, so
`Ring.KrullDimLE 1 (R ⧸ P)` follows from zero-dimensionality of `S`.

Route: `Ideal.Quotient.factor hP : S →+* R ⧸ P` is surjective
(`Ideal.Quotient.factor_surjective`), hence
`ringKrullDim (R ⧸ P) ≤ ringKrullDim S` (`ringKrullDim_le_of_surjective`),
and `ringKrullDim S ≤ 1` is `hZd` via `Ring.krullDimLE_iff`.

## References

* `Mathlib/RingTheory/KrullDimension/Basic.lean`, `ringKrullDim`,
  `Ring.KrullDimLE`, `ringKrullDim_le_of_surjective`
  (`ringKrullDim S ≤ ringKrullDim R` for `f : R →+* S` surjective),
  `Ring.krullDimLE_iff` (`Ring.KrullDimLE n R ↔ ringKrullDim R ≤ ↑n`).
* `Mathlib/RingTheory/Ideal/Quotient/Defs.lean`, `Ideal.Quotient.factor`
  (quotient by a smaller ideal maps to quotient by a larger one),
  `Ideal.Quotient.factor_surjective`.
* `Formalization/Appendix_FixedPoint/BezoutChain/
  Statement/Definitions.lean`, `coneQuotient`, `IsZeroDimensional`.

Deviation note: the original unmixedness plan §0 routes this through
`coheight_comap_of_surjective` in `Ideal/Maps.lean`; the in-tree name is
`Ideal.coheight_comap_of_surjective` (`Maps.lean`). The
`ringKrullDim_le_of_surjective` route above is the verified equivalent used
here and yields the same `Ring.KrullDimLE` conclusion. -/
theorem krullDimLE_quotient_of_contains_span (n : ℕ) (K : Type*) [Field K]
    (G : Fin (n + 1) → MvPolynomial (Fin (n + 2)) K)
    (hZd : IsZeroDimensional n K G)
    (P : Ideal (MvPolynomial (Fin (n + 2)) K))
    (hP : Ideal.span (Set.range G) ≤ P) :
    Ring.KrullDimLE 1 (MvPolynomial (Fin (n + 2)) K ⧸ P) := by
  have hsurj : Function.Surjective
      (Ideal.Quotient.factor hP :
        coneQuotient n K G →+* MvPolynomial (Fin (n + 2)) K ⧸ P) :=
    Ideal.Quotient.factor_surjective hP
  have hdimS : ringKrullDim (coneQuotient n K G) ≤ 1 :=
    Ring.krullDimLE_iff.mp hZd
  refine Ring.krullDimLE_iff.mpr ?_
  exact (ringKrullDim_le_of_surjective _ hsurj).trans hdimS

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
