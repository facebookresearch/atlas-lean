/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightQSupportCoordinates
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightFullQSupportProjection
public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQPhaseCoordinates

/-! The twenty-three selected covectors are original preferred-short conjugation phases. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine even witnesses together with the original odd label32 at coordinate1. -/
def generatedFifthRootEightFullQSupportIndex (j : Fin 23) : GriessShortIndex :=
  if h : j.val < 22 then generatedFifthRootEightQSupportIndex ⟨j.val, h⟩
  else Sum.inr (Sum.inr (32, 1))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
-- Bind each covector entry to the entire original preferred short lift.
/-- The stated phase matrix is the actual modulation-translation covector of every selected lift. -/
theorem generatedFifthRootEight_full_Q_support_phase_matrix_finite : ∀ j : Fin 23, ∀ i : Fin 24,
    generatedFifthRootEightFullQSupportPhaseMatrix j i =
      Fin.append
        (spinModulation (generatedAxisGlobalShortQFinite (generatedFifthRootEightFullQSupportIndex j)))
        (spinTranslation
          (generatedAxisGlobalShortQFinite (generatedFifthRootEightFullQSupportIndex j))) i := by
  decide +kernel

/-- Every literal matrix equation is the actual original selected-short conjugation phase. -/
theorem generatedFifthRootEight_full_Q_support_phase_coordinates (q : Q) (j : Fin 23) :
    Multiplicative.toAdd (localAxisQPhase (generatedFifthRootEightFullQSupportIndex j) q) =
      (generatedFifthRootEightFullQSupportPhaseMatrix *ᵥ Multiplicative.toAdd q.base) j := by
  rw [generatedTenth_Q_phase_coordinates]
  change _ = generatedFifthRootEightFullQSupportPhaseMatrix j ⬝ᵥ Multiplicative.toAdd q.base
  apply congrArg (fun v : Fin 24 → ZMod 2 => v ⬝ᵥ Multiplicative.toAdd q.base)
  funext i
  have h := generatedFifthRootEight_full_Q_support_phase_matrix_finite j i
  rw [generatedAxisGlobalShortQFinite_actual] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
