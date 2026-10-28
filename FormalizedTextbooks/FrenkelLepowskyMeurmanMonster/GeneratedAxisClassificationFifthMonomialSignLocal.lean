/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalCompletionProjection

/-! Actual local lifts of the original Golay sign words, using the proved full centralizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each original source sign word has an actual local lift by the proved centralizer equality. -/
theorem generatedFifth_sign_local_exists (d : Fin 4096) (ε : ZMod 2) :
    ∃ h : H, localIntoGenerated h = sourceGeneratedY d ε := by
  have hm := sourceGeneratedY_mem_centralizer d ε
  rw [generatedCentralizer_eq_local_range] at hm
  exact hm

/-- The actual local element above an original source sign word. -/
noncomputable def generatedFifthSignLocal (d : Fin 4096) (ε : ZMod 2 := 0) : H :=
  Classical.choose (generatedFifth_sign_local_exists d ε)

/-- The chosen actual local lift is exactly the original source word in the generated group. -/
theorem generatedFifth_sign_local_generated (d : Fin 4096) (ε : ZMod 2) :
    localIntoGenerated (generatedFifthSignLocal d ε) = sourceGeneratedY d ε :=
  Classical.choose_spec (generatedFifth_sign_local_exists d ε)

/-- Its actual Conway projection is the prescribed genuine Golay sign isometry. -/
theorem generatedFifth_sign_local_projection (d : Fin 4096) (ε : ZMod 2) :
    projH (generatedFifthSignLocal d ε) =
      (QuotientGroup.mk (golaySignIsometry (sourceGeneratedSignCode d)) : Co1) :=
  sourceGeneratedY_lift_projection d ε _ (generatedFifth_sign_local_generated d ε)

/-- The local Griess action is the exact original source word action. -/
theorem generatedFifth_sign_local_action (d : Fin 4096) (ε : ZMod 2) :
    rhoLocal (generatedFifthSignLocal d ε) = (sourceGeneratedY d ε).val :=
  congrArg Subtype.val (generatedFifth_sign_local_generated d ε)

/-- The local sign action is inverse triality, original code action, then triality. -/
theorem generatedFifth_sign_local_apply (d : Fin 4096) (ε : ZMod 2) (x : GriessSpace) :
    rhoLocal (generatedFifthSignLocal d ε) x =
      sExtra⁻¹ (rhoLocal (inclQ (sourceQCode d ε)) (sExtra x)) := by
  rw [generatedFifth_sign_local_action]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
