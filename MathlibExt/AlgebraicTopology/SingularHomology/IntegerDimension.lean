/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerGrading
public import MathlibExt.AlgebraicTopology.SingularHomology.Reduced

/-!
# Dimension computations for integer-graded singular homology
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

universe w v u

variable (C : Type u) [Category.{v} C] [Abelian C] [HasCoproducts.{w} C]

/-- Integer-graded singular homology of a point vanishes in every nonzero degree.

This transports the natural-graded `isZero_singularHomology_punit` across
`singularHomologyNatToIntIso` for non-negative degrees, and uses the
negativity lemma `isZero_singularHomologyIntFunctor_of_neg` for negative degrees. -/
theorem isZero_singularHomologyInt_punit (R : C) (z : ℤ) (hz : z ≠ 0) :
    IsZero ((singularHomologyIntFunctor C R z).obj (TopCat.of PUnit)) := by
  by_cases hzNeg : z < 0
  · exact isZero_singularHomologyIntFunctor_of_neg C R z hzNeg (TopCat.of PUnit)
  · have hzNonNeg : 0 ≤ z := by omega
    have hzEq : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzNonNeg
    have hToNatNe : z.toNat ≠ 0 := by
      intro h
      apply hz
      calc z = (z.toNat : ℤ) := hzEq.symm
        _ = ((0 : ℕ) : ℤ) := by rw [h]
        _ = 0 := by simp
    have hNat : IsZero (((singularHomologyFunctor C z.toNat).obj R).obj (TopCat.of PUnit)) :=
      isZero_singularHomology_punit C R z.toNat hToNatNe
    have hInt :
        IsZero ((singularHomologyIntFunctor C R (z.toNat : ℤ)).obj (TopCat.of PUnit)) :=
      hNat.of_iso ((singularHomologyNatToIntIso C R z.toNat).app (TopCat.of PUnit))
    rw [hzEq] at hInt
    exact hInt

/-- Canonical degree-zero isomorphism for integer-graded singular homology of a point.

Composes the integer-to-natural comparison at `0` with the accepted
`singularHomologyPUnitZeroIso`. -/
noncomputable def singularHomologyIntPUnitZeroIso (R : C) :
    (singularHomologyIntFunctor C R (0 : ℤ)).obj (TopCat.of PUnit) ≅ R :=
  (singularHomologyNatToIntIso C R 0).app (TopCat.of PUnit) ≪≫
    singularHomologyPUnitZeroIso C R

@[simp]
theorem singularHomologyIntPUnitZeroIso_hom (R : C) :
    (singularHomologyIntPUnitZeroIso C R).hom =
      ((singularHomologyNatToIntIso C R 0).app (TopCat.of PUnit)).hom ≫
        (singularHomologyPUnitZeroIso C R).hom := by
  simp [singularHomologyIntPUnitZeroIso]

end AlgebraicTopology
