/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Quasicategory.RightFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryLiftingCore

/-!
# Right horn lifting

Right fibrations lift all horns with nonzero missing vertex, including the
one-dimensional target horn. The original base map and all whole horn
problems are retained. This is the dual orientation of `LeftFibration`.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty
open scoped Simplicial

namespace SSet

/-- The original right horn inclusions, including the target horn in dimension one. -/
inductive rightHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : ℕ} (i : Fin (n + 2)) (hi : 0 < i) :
    rightHornInclusions Λ[n + 1, i].ι

/-- Every positive-index horn belongs to the right horn family. -/
theorem horn_ι_mem_rightHornInclusions {n : ℕ} {i : Fin (n + 1)}
    (hi : 0 < i) : rightHornInclusions (horn.{u} n i).ι := by
  obtain _ | n := n
  · have : i = 0 := Fin.ext (by omega)
    simp [this] at hi
  · exact ⟨i, hi⟩

/-- Every inner horn is a right horn. -/
theorem innerHornInclusions_le_rightHornInclusions :
    innerHornInclusions.{u} ≤ rightHornInclusions := by
  intro _ _ _ h
  obtain @⟨n, i, h0, _⟩ := h
  exact ⟨i, h0⟩

/-- The right lifting class of the actual right horns. -/
def rightFibrations : MorphismProperty SSet.{u} := rightHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange, IsStableUnderRetracts

/-- The canonical right-fibration record lies in the original right lifting class. -/
theorem RightFibration.mem {X B : SSet.{u}} {p : X ⟶ B} [RightFibration p] :
    rightFibrations p := by
  intro A₀ B₀ i hi
  obtain @⟨n, k, hk⟩ := hi
  exact RightFibration.hasLiftingProperty_horn k hk

/-- Membership in the original right lifting class gives the canonical record. -/
theorem rightFibration_of_mem_rightFibrations {X B : SSet.{u}} {p : X ⟶ B}
    (h : rightFibrations p) : RightFibration p := by
  constructor
  intro n i hi
  exact h _ (horn_ι_mem_rightHornInclusions hi)

/-- Right horn lifting includes inner horn lifting. -/
theorem rightFibrations_le_innerFibrations :
    rightFibrations.{u} ≤ innerFibrations :=
  antitone_rlp innerHornInclusions_le_rightHornInclusions

/-- Lifting all right horns gives the native right-fibration record. -/
theorem rightFibration_of_hasLiftingProperty_horn {X B : SSet.{u}} {p : X ⟶ B}
    (h : ∀ {n : ℕ} {i : Fin (n + 1)}, 0 < i → HasLiftingProperty Λ[n, i].ι p) :
    RightFibration p := by
  constructor
  intro n i hi
  exact h hi

/-- Boundary lifting implies right horn lifting. -/
theorem rightFibration_of_rlp_I {X B : SSet.{u}} {p : X ⟶ B}
    (hp : modelCategoryQuillen.I.rlp p) : RightFibration p := by
  refine rightFibration_of_hasLiftingProperty_horn (fun {n i} _ => ?_)
  have hi : modelCategoryQuillen.I.rlp.llp Λ[n, i].ι :=
    modelCategoryQuillen.llp_rlp_I ▸ monomorphisms.infer_property _
  exact hi _ hp

end SSet
