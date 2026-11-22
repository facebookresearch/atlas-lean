/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FiniteLatchingFromOriginalAllOperators

/-!
# The final finite stage and the full outer latching subcomplex

The last finite degeneracy stage is naturally isomorphic to the complete outer latching subcomplex in the next degree, preserving its inclusion into the row. Sharp row maps and weak relative comparisons for every simplex operator therefore give sharp full latching maps and weak incoming comparisons in every positive degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkFullLatching
open SharpComparisonDraft RezkCompatiblePushout

/-- The actual last finite latching stage is the whole latching object. -/
def lastStageIso (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (outerLatchingStage X n (Fin.last n) : SSet.{u}) ≅ outerLatching X (n + 1) :=
  Subcomplex.eqToIso (outerLatchingStage_last X n)

@[reassoc (attr := simp)]
theorem lastStageIso_hom_ι (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (lastStageIso X n).hom ≫ (outerLatching X (n + 1)).ι =
      (outerLatchingStage X n (Fin.last n)).ι := by
  simp [lastStageIso, Subcomplex.eqToIso]

/-- Naturality identifies the two original full latching maps, with no new map. -/
theorem lastStageIso_naturality {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y) (n : ℕ) :
    (lastStageIso X n).hom ≫ outerLatchingMap eta (n + 1) =
      outerLatchingStageMap eta n (Fin.last n) ≫ (lastStageIso Y n).hom := by
  apply (cancel_mono (outerLatching Y (n + 1)).ι).mp
  simp only [Category.assoc, outerLatchingMap_ι, lastStageIso_hom_ι_assoc,
    lastStageIso_hom_ι, outerLatchingStageMap_ι]

/-- The original row-sharp and ALL-operator inputs derive the whole latching
Sharp and incoming HC assertions. No finite-stage output is a premise. -/
theorem sharp_and_incoming_from_original_all_operators
    {X Y : SimplicialObject SSet.{u}} (eta : X ⟶ Y)
    (hrows : ∀ n : SimplexCategory, Sharp (eta.app (op n)))
    (hoperators : ∀ {n m : SimplexCategory} (f : n ⟶ m),
      WeakEquivalence (EquifibredDiagonal.relativeComparison eta f)) (n : ℕ) :
    Sharp (outerLatchingMap eta (n + 1)) ∧
      WeakEquivalence
        (pullback.lift (outerLatching X (n + 1)).ι (outerLatchingMap eta (n + 1))
          (outerLatchingMap_ι eta (n + 1)).symm ≫
          comparison (eta.app (op ⦋n + 1⦌)) (outerLatching Y (n + 1)).ι) := by
  have finite := RezkFiniteFromAllOperators.all_finite_from_original_operators
    eta hrows hoperators n (Fin.last n)
  let E : Arrow.mk (outerLatchingStageMap eta n (Fin.last n)) ≅
      Arrow.mk (outerLatchingMap eta (n + 1)) :=
    Arrow.isoMk (lastStageIso X n) (lastStageIso Y n) (lastStageIso_naturality eta n)
  have wholeSharp : Sharp (outerLatchingMap eta (n + 1)) :=
    (SharpCoproductClosure.sharp_arrowIso_iff E).mp finite.1
  let first : CommSq (outerLatchingStage X n (Fin.last n)).ι
      (outerLatchingStageMap eta n (Fin.last n)) (eta.app (op ⦋n + 1⦌))
      (outerLatchingStage Y n (Fin.last n)).ι :=
    CommSq.mk (outerLatchingStageMap_ι eta n (Fin.last n)).symm
  let second : CommSq (outerLatching X (n + 1)).ι (outerLatchingMap eta (n + 1))
      (eta.app (op ⦋n + 1⦌)) (outerLatching Y (n + 1)).ι :=
    CommSq.mk (outerLatchingMap_ι eta (n + 1)).symm
  have wholeHC := (hc_weakSquare_iff first second
    (lastStageIso X n).hom (𝟙 _) (lastStageIso Y n).hom (𝟙 _)
    (by simp) (lastStageIso_naturality eta n) (by simp) (by simp)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mp finite.2
  exact ⟨wholeSharp, wholeHC⟩

end SSet.RezkFullLatching
