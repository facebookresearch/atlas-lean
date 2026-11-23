/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.SingularHomology.IntegerData
public import MathlibExt.AlgebraicTopology.SingularHomology.RelativeHomologyCoproducts

/-!
# Additivity of integer-graded singular homology
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicTopology

universe u v w

noncomputable instance singularHomologyIntData_isAdditive
    {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [AB4OfSize.{w} C]
    (R : C) :
    (singularHomologyIntData C R).IsAdditive where
  preservesDiscreteCoproducts := by
    intro z J
    by_cases hz : z < 0
    · let F := relativeSingularHomologyIntFunctor C R z
      have hF : IsZero F := by
        rw [Functor.isZero_iff]
        intro P
        exact isZero_relativeSingularHomologyIntFunctor_of_neg C R z hz P
      exact F.preservesColimitsOfShape_of_isZero hF (Discrete J)
    · have hzNonNeg : 0 ≤ z := by omega
      have hzEq : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzNonNeg
      have : PreservesColimitsOfShape (Discrete J)
          (relativeSingularHomologyFunctor C R z.toNat) := by
        have : PreservesFiniteLimits (colim (J := Discrete J) (C := C)) :=
          inferInstance
        have : PreservesFiniteColimits (colim (J := Discrete J) (C := C)) :=
          inferInstance
        have : (colim (J := Discrete J) (C := C)).PreservesHomology :=
          inferInstance
        change PreservesColimitsOfShape (Discrete J)
          (relativeSingularChainFunctor C R ⋙
            HomologicalComplex.homologyFunctor C (ComplexShape.down ℕ) z.toNat)
        infer_instance
      have hPres : PreservesColimitsOfShape (Discrete J)
          (relativeSingularHomologyIntFunctor C R
            (z.toNat : ℤ)) :=
        preservesColimitsOfShape_of_natIso
          (relativeSingularHomologyNatToIntIso
            C R z.toNat).symm
      rw [hzEq] at hPres
      exact hPres

end AlgebraicTopology
