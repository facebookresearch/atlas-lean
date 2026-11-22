/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialSkeletalFiltration
import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutHCTransport
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Predecessor and overlap identifications for finite latching stages

The stage before a successor degeneracy attachment equals the preceding finite latching stage. Natural arrow isomorphisms identify the corresponding diagram maps and identify the successor source-overlap map with a lower-dimensional latching-stage map. These identifications transport the weak incoming-comparison condition between the predecessor and before-successor descriptions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkFiniteStageGeometry
open SharpComparisonDraft RezkCompatiblePushout

/-- The preceding part at a successor index is the actual previous same-degree stage. -/
theorem before_succ_eq (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageBefore X (n + 1) r.succ = outerLatchingStage X (n + 1) r.castSucc := by
  simp only [outerLatchingStageBefore, outerLatchingStage, Fin.lt_def,
    Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc, Nat.lt_succ_iff]

/-- Both literal equality Isos identify the preceding map with the earlier stage map. -/
def beforeArrowIso {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    Arrow.mk (outerLatchingStageBeforeMap eta (n + 1) r.succ) ≅
      Arrow.mk (outerLatchingStageMap eta (n + 1) r.castSucc) := by
  let ex := Subcomplex.eqToIso (before_succ_eq X n r)
  let ey := Subcomplex.eqToIso (before_succ_eq Y n r)
  refine Arrow.isoMk ex ey ?_
  apply (cancel_mono (outerLatchingStage Y (n + 1) r.castSucc).ι).mp
  simp [ex, ey, Category.assoc]

/-- The lower-degree overlap map is identified with the actual lower latching stage. -/
def overlapArrowIso {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    Arrow.mk (outerLatchingStageSourceOverlapMap eta (n + 1) r.succ) ≅
      Arrow.mk (outerLatchingStageMap eta n r) := by
  let ex := Subcomplex.eqToIso (outerLatchingStageSourceOverlap_succ X n r)
  let ey := Subcomplex.eqToIso (outerLatchingStageSourceOverlap_succ Y n r)
  refine Arrow.isoMk ex ey ?_
  apply (cancel_mono (outerLatchingStage Y n r).ι).mp
  simp [ex, ey, Category.assoc]

/-- The preceding-stage inclusion HC is exactly the earlier same-degree incoming invariant. -/
theorem before_incoming_iff {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    WeakEquivalence
      (pullback.lift (outerLatchingStageBefore X (n + 1) r.succ).ι
        (outerLatchingStageBeforeMap eta (n + 1) r.succ)
        (outerLatchingStageBeforeMap_ι eta (n + 1) r.succ).symm ≫
        comparison (eta.app (op ⦋(n + 1) + 1⦌)) (outerLatchingStageBefore Y (n + 1) r.succ).ι) ↔
      WeakEquivalence
        (pullback.lift (outerLatchingStage X (n + 1) r.castSucc).ι
          (outerLatchingStageMap eta (n + 1) r.castSucc)
          (outerLatchingStageMap_ι eta (n + 1) r.castSucc).symm ≫
          comparison (eta.app (op ⦋(n + 1) + 1⦌)) (outerLatchingStage Y (n + 1) r.castSucc).ι) := by
  let ex := Subcomplex.eqToIso (before_succ_eq X n r)
  let ey := Subcomplex.eqToIso (before_succ_eq Y n r)
  have hmap : outerLatchingStageBeforeMap eta (n + 1) r.succ ≫ ey.hom =
      ex.hom ≫ outerLatchingStageMap eta (n + 1) r.castSucc := by
    exact (beforeArrowIso eta n r).hom.w.symm
  exact hc_weakSquare_iff
    (CommSq.mk (outerLatchingStageBeforeMap_ι eta (n + 1) r.succ).symm)
    (CommSq.mk (outerLatchingStageMap_ι eta (n + 1) r.castSucc).symm)
    ex.hom (𝟙 _) ey.hom (𝟙 _)
    (by simp [ex]) hmap (by simp) (by simp [ey])
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)

end SSet.RezkFiniteStageGeometry
