/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPrimitivePackedActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinSourceQReplayData

/-! Genuine full extraspecial primitive action, independent of full-word source certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-- Exact packed vector and full central-bit obligations for every actual normalized prefix. -/
def generatedNinthLowerSpinPrimitivePackedReplayStepCondition (i : Fin 11) (n : Fin 378)
    (j : Fin 24) : Prop :=
  n.val < (generatedNinthLowerSpinSourceWord i).length →
    generatedNinthLowerSpinPrimitivePackedCondition
      (generatedNinthLowerSpinSourceQReplayLetter i n)
      (generatedNinthLowerSpinSourceQReplayWord i (Fin.castAdd 1 n) j)
      (generatedNinthLowerSpinSourceQReplayWord i ⟨n.val + 1, by omega⟩ j)

/-- The source normalized prefix decode is the entire original Q label used by the packed model. -/
theorem generatedNinth_lower_spin_primitive_packed_replay_prefix (i : Fin 11) (n : Fin 379)
    (j : Fin 24) : generatedNinthLowerSpinSourceQReplayPrefix i n j =
      generatedNinthLowerSpinPrimitivePackedQ (generatedNinthLowerSpinSourceQReplayWord i n j) :=
  rfl

/-- Packed source-step checks establish the unchanged ORIGINAL primitive-prefix obligations. -/
theorem generatedNinth_lower_spin_primitive_packed_replay_step (i : Fin 11) (n : Fin 378)
    (j : Fin 24) (h : generatedNinthLowerSpinPrimitivePackedReplayStepCondition i n j) :
    generatedNinthLowerSpinSourceQReplayStepCondition i n j := by
  intro hn
  rw [generatedNinth_lower_spin_primitive_packed_replay_prefix,
    generatedNinth_lower_spin_primitive_packed_replay_prefix]
  exact generatedNinth_lower_spin_primitive_evaluation_of_packed _ _ _ (h hn)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
