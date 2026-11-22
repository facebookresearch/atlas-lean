/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltration
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpCoproductClosure

/-!
# The first sharpness cases in the original skeletal/latching proof

The actual degeneracy range and the zero finite latching stage are
transported from the same preceding row by constructed Arrow Isos.
No sharpness of the full diagonal or an attachment map is assumed.
The generic row-sharp hypothesis must be derived from the original
row fibrations in the completion application.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkDiagonalSharpBase
open SharpComparisonDraft

/-- The original degeneracy-range map is the SAME row map through both range Isos. -/
def degeneracyRangeArrowIso {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    Arrow.mk (η.app (op ⦋n⦌)) ≅ Arrow.mk (outerDegeneracyRangeMap η n r) := by
  letI : Mono (X.σ r) := SimplicialObject.mono_sigma X r
  letI : Mono (Y.σ r) := SimplicialObject.mono_sigma Y r
  refine Arrow.isoMk (asIso (Subcomplex.toRange (X.σ r)))
    (asIso (Subcomplex.toRange (Y.σ r))) ?_
  change Subcomplex.toRange (X.σ r) ≫ outerDegeneracyRangeMap η n r =
    η.app (op ⦋n⦌) ≫ Subcomplex.toRange (Y.σ r)
  apply (cancel_mono (Subcomplex.range (Y.σ r)).ι).mp
  calc
    (Subcomplex.toRange (X.σ r) ≫ outerDegeneracyRangeMap η n r) ≫
        (Subcomplex.range (Y.σ r)).ι =
      Subcomplex.toRange (X.σ r) ≫
        ((Subcomplex.range (X.σ r)).ι ≫ η.app (op ⦋n + 1⦌)) := by
      rw [Category.assoc, outerDegeneracyRangeMap_ι]
    _ = X.σ r ≫ η.app (op ⦋n + 1⦌) := by
      rw [← Category.assoc, Subcomplex.toRange_ι]
    _ = η.app (op ⦋n⦌) ≫ Y.σ r := SimplicialObject.σ_naturality η r
    _ = (η.app (op ⦋n⦌) ≫ Subcomplex.toRange (Y.σ r)) ≫
        (Subcomplex.range (Y.σ r)).ι := by
      rw [Category.assoc, Subcomplex.toRange_ι]

/-- All four Arrow legs are the actual range factor and its native inverse. -/
theorem degeneracyRangeArrowIso_fourLegs {X Y : SimplicialObject SSet.{u}}
    (η : X ⟶ Y) (n : ℕ) (r : Fin (n + 1)) :
    letI : Mono (X.σ r) := SimplicialObject.mono_sigma X r
    letI : Mono (Y.σ r) := SimplicialObject.mono_sigma Y r
    (degeneracyRangeArrowIso η n r).hom.left = Subcomplex.toRange (X.σ r) ∧
      (degeneracyRangeArrowIso η n r).hom.right = Subcomplex.toRange (Y.σ r) ∧
      (degeneracyRangeArrowIso η n r).inv.left = inv (Subcomplex.toRange (X.σ r)) ∧
      (degeneracyRangeArrowIso η n r).inv.right = inv (Subcomplex.toRange (Y.σ r)) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every prescribed degeneracy range inherits sharpness from its original row. -/
theorem degeneracyRangeMap_sharp {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) (hrow : Sharp (η.app (op ⦋n⦌))) :
    Sharp (outerDegeneracyRangeMap η n r) :=
  (SharpCoproductClosure.sharp_arrowIso_iff (degeneracyRangeArrowIso η n r)).mp hrow

/-- The first finite latching-stage map is the SAME row map through the actual σ₀ Isos. -/
def zeroStageArrowIso {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y) (n : ℕ) :
    Arrow.mk (η.app (op ⦋n⦌)) ≅ Arrow.mk (outerLatchingStageMap η n 0) := by
  refine Arrow.isoMk (outerLatchingStage_zero_iso X n) (outerLatchingStage_zero_iso Y n) ?_
  apply (cancel_mono (outerLatchingStage Y n 0).ι).mp
  calc
    ((outerLatchingStage_zero_iso X n).hom ≫ outerLatchingStageMap η n 0) ≫
        (outerLatchingStage Y n 0).ι =
      (outerLatchingStage_zero_iso X n).hom ≫
        ((outerLatchingStage X n 0).ι ≫ η.app (op ⦋n + 1⦌)) := by
      rw [Category.assoc, outerLatchingStageMap_ι]
    _ = X.σ (0 : Fin (n + 1)) ≫ η.app (op ⦋n + 1⦌) := by
      rw [← Category.assoc, outerLatchingStage_zero_iso_hom_ι]
    _ = η.app (op ⦋n⦌) ≫ Y.σ (0 : Fin (n + 1)) :=
      SimplicialObject.σ_naturality η (0 : Fin (n + 1))
    _ = (η.app (op ⦋n⦌) ≫ (outerLatchingStage_zero_iso Y n).hom) ≫
        (outerLatchingStage Y n 0).ι := by
      rw [Category.assoc, outerLatchingStage_zero_iso_hom_ι]

/-- The sharpness induction starts at the constructed first latching stage. -/
theorem zeroStageMap_sharp {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (hrow : Sharp (η.app (op ⦋n⦌))) :
    Sharp (outerLatchingStageMap η n 0) :=
  (SharpCoproductClosure.sharp_arrowIso_iff (zeroStageArrowIso η n)).mp hrow

end SSet.RezkDiagonalSharpBase
