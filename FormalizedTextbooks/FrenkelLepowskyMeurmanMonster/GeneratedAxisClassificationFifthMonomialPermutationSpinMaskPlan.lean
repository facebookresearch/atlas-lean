/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpinMaskChecker

/-! Structural soundness for complete signed spin plans certified by bounded mask edges. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A source letter, full next model, transpose rows, and raw product phase rows. -/
abbrev generatedFifthSpinMaskStep (ι : Type) :=
  ι × generatedFifthSpinMaskRows × (Fin 12 → ℕ) × (Fin 12 → ℕ)

/-- Decode every literal intermediate signed model into the genuine matrix plan. -/
def generatedFifthSpinMaskPlan {ι : Type} (p : List (generatedFifthSpinMaskStep ι)) :
    RepresentativeSpinPlan ι := p.map (fun x => (x.1, generatedFifthSpinMaskRowsModel x.2.1))

/-- Only exact finite row products and quadratic coefficient comparisons are checked. -/
def generatedFifthSpinMaskPlanCheck {ι : Type} (letters : ι → generatedFifthSpinMaskRows) :
    generatedFifthSpinMaskRows → List (generatedFifthSpinMaskStep ι) → Prop
  | _, [] => True
  | a, x :: xs =>
      generatedFifthSpinMaskEdgeCheck a (letters x.1) x.2.1 x.2.2.1 x.2.2.2 ∧
        generatedFifthSpinMaskPlanCheck letters x.2.1 xs

/-- Structural finite decision procedure for the mask certificate. -/
def generatedFifthSpinMaskPlanDecision {ι : Type} (letters : ι → generatedFifthSpinMaskRows)
    (a : generatedFifthSpinMaskRows) (p : List (generatedFifthSpinMaskStep ι)) :
    Decidable (generatedFifthSpinMaskPlanCheck letters a p) := by
  induction p generalizing a with
  | nil => exact isTrue trivial
  | cons x xs ih =>
    letI := ih x.2.1
    change Decidable (_ ∧ generatedFifthSpinMaskPlanCheck letters x.2.1 xs)
    infer_instance

/-- The ordinary recursive checker supplies decidability without any validity assumption. -/
instance generatedFifthSpinMaskPlanDecidable {ι : Type}
    (letters : ι → generatedFifthSpinMaskRows) (a : generatedFifthSpinMaskRows)
    (p : List (generatedFifthSpinMaskStep ι)) :
    Decidable (generatedFifthSpinMaskPlanCheck letters a p) :=
  generatedFifthSpinMaskPlanDecision letters a p

/-- Checked finite row certificates imply the entire original signed matrix plan. -/
theorem generatedFifth_spin_mask_plan_sound {ι : Type}
    (letters : ι → generatedFifthSpinMaskRows) (models : ι → RepresentativeSpinModel)
    (hm : ∀ l, generatedFifthSpinMaskRowsModel (letters l) = models l)
    (a : generatedFifthSpinMaskRows) (p : List (generatedFifthSpinMaskStep ι))
    (hc : generatedFifthSpinMaskPlanCheck letters a p) :
    representativeSpinPlanValid models (generatedFifthSpinMaskRowsModel a)
      (generatedFifthSpinMaskPlan p) := by
  induction p generalizing a with
  | nil => trivial
  | cons x xs ih =>
    refine ⟨?_, ih _ hc.2⟩
    rw [← hm x.1]
    exact generatedFifth_spin_mask_edge_sound _ _ _ _ _ hc.1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
