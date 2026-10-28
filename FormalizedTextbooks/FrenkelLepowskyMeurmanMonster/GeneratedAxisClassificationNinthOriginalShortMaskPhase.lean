/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortMaskRecognition

/-! A checked intrinsic mask determines the complete preferred source lift, whose coefficient
is zero. Its original central phase can therefore be evaluated without recomputing the Leech
inverse. The scalar bits of the genuine nine-factor automorphism are retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The intrinsic preferred lift of a packed binary vector, with central coefficient zero. -/
def generatedNinthMaskPreferredQ (n : ℕ) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode n), 1⟩

/-- The exact original source phase evaluated on a preferred packed lift. -/
def generatedNinthMaskPreferredPhase (n : ℕ) : ZMod 2 :=
  generatedNinthSelectedPhase (generatedNinthMaskPreferredQ n)

/-- An actual source-mask equation identifies the full preferred lift, including its coefficient. -/
theorem generatedNinth_original_short_Q_of_mask
    (a : generatedNinthOriginalShortLabel) (n : ℕ)
    (hsource : toAdd (generatedNinthOriginalShortQ a).base =
      monsterCo1GeometryBinaryMaskDecode n) :
    generatedNinthOriginalShortQ a = generatedNinthMaskPreferredQ n := by
  apply NormalizedCocycleExtension.Extension.ext
  · exact toAdd.injective hsource
  · rfl

/-- A recognized target retains its full source central phase through the packed evaluation. -/
theorem generatedNinth_original_short_coefficient_of_mask_phase
    (a : generatedNinthOriginalShortLabel) (s : GriessShortIndex) (n m : ℕ)
    (hsource : toAdd (generatedNinthOriginalShortQ a).base =
      monsterCo1GeometryBinaryMaskDecode n)
    (htarget : toAdd (monsterNortonShortQ s).base =
      monsterCo1GeometryBinaryMaskDecode m)
    (himage : sixthFrameOrbitMaskApply generatedNinthQBinaryColumns n = m) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 s =
        qSign (generatedNinthMaskPreferredPhase n) *
          ((generatedNinthOriginalShortNumerator a : ℝ) / 16) := by
  rw [generatedNinth_original_short_coefficient_of_masks a s n m hsource htarget himage,
    generatedNinth_original_short_Q_of_mask a n hsource]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
