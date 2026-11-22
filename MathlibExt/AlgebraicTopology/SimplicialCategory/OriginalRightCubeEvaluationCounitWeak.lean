/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeMaximumWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCubeMappingWeakComparison

/-!
# Genuine same original quotient-cube evaluation counit weakness

The full original maximum is weak on every actual input. Its exact
naturality makes the SAME quotient-cube realization recognize the
entire original scalar weak class. The existing genuine Kan Hom
comparison then proves weakness of the actual original scalar
realization/singular evaluation counit.
-/

noncomputable section
universe u
open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- The SAME original full quotient-cube realization recognizes every original scalar realization weak map. -/
theorem map_weak_iff {K L : SSet.{u}} (f : K ⟶ L) :
    SSet.realizationWeakEquivalences (map f) ↔ SSet.realizationWeakEquivalences f := by
  let W := SSet.realizationWeakEquivalences.{u}
  exact (W.postcomp_iff _ _ (maximum_weak L)).symm.trans
    ((Iff.of_eq (congrArg (fun g : object K ⟶ L => W g) (maximum_naturality f))).trans
      (W.precomp_iff _ _ (maximum_weak K)))

/-- The SAME actual scalar adjunction counit is the full original coefficient colimit evaluation. -/
def evaluationCounit (H : SSet.{u}) : object (singular.obj H) ⟶ H :=
  fromSingular (𝟙 (singular.obj H))

/-- Every full original singular coefficient is retained literally by the actual evaluation counit. -/
theorem insertion_evaluationCounit (H : SSet.{u}) (e : (singular.obj H).Elementsᵒᵖ) :
    insertion (singular.obj H) e ≫ evaluationCounit H = e.unop.val :=
  insertion_fromSingular _ _

/-- The actual original scalar evaluation counit is precisely the genuine adjunction counit, including all coefficients.
-/
theorem evaluationCounit_original (H : SSet.{u}) :
    evaluationCounit H = adjunction.counit.app H := by
  have h := adjunction.homEquiv_symm_id H
  have he : adjunction.homEquiv = homEquiv := by
    exact Adjunction.mkOfHomEquiv_homEquiv _
  rw [he] at h
  exact h

/-- The SAME original maximum-induced singular comparison has the original full coefficient map. -/
def singularComparison (H : SSet.{u}) : H ⟶ singular.obj H :=
  CubeMappingSpace.comparison H

/-- The actual original full maximum factors through the SAME original singular comparison and evaluation counit. -/
theorem comparison_evaluationCounit (H : SSet.{u}) :
    map (singularComparison H) ≫ evaluationCounit H = maximum H := by
  apply colimit.hom_ext
  intro e
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ evaluationCounit H) (insertion_map (singularComparison H) e)).trans
      ((insertion_evaluationCounit H _).trans (insertion_maximum H e).symm))

/-- The genuine SAME original scalar realization/singular evaluation counit is weak for every original Kan coefficient.
-/
theorem evaluationCounit_weak (H : SSet.{u}) [SSet.KanComplex H] :
    SSet.realizationWeakEquivalences (evaluationCounit H) := by
  have hComp : SSet.realizationWeakEquivalences (singularComparison H) :=
    CubeMappingSpace.comparison_weak H
  have hQ : SSet.realizationWeakEquivalences (map (singularComparison H)) := (map_weak_iff _).mpr hComp
  exact SSet.realizationWeakEquivalences.of_precomp _ _ hQ
    ((comparison_evaluationCounit H).symm ▸ maximum_weak H)

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
