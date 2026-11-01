/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiSelectedPhase
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBinaryMasks

/-! Complete preferred source masks retain all 24 binary coordinates and the zero central bit. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Joining two coefficient masks places modulation in the upper twelve positions. -/
def generatedSixthXiJoinMasks (u : Fin 4096) (m : ℕ) : ℕ := u.val ||| (m <<< 12)

/-- Bit joining equals the genuine ordered hyperbolic code/cocode coordinate vector. -/
theorem generatedSixth_xi_join_masks_decode (u : Fin 4096) (m : ℕ) :
    monsterCo1GeometryBinaryMaskDecode (n := 24) (generatedSixthXiJoinMasks u m) =
      Fin.append (golayLabelCoefficients u) (monsterCo1GeometryBinaryMaskDecode (n := 12) m) := by
  funext i
  refine Fin.addCases (m := 12) (n := 12) (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    change (if (u.val ||| (m <<< 12)).testBit j.val then (1 : ZMod 2) else 0) =
      if u.val.testBit j.val then 1 else 0
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    simp [show ¬ j.val ≥ 12 by omega]
  · rw [Fin.append_right]
    change (if (u.val ||| (m <<< 12)).testBit (12 + j.val) then (1 : ZMod 2) else 0) =
      if m.testBit j.val then 1 else 0
    have hu : u.val.testBit (12 + j.val) = false := by
      apply Nat.testBit_eq_false_of_lt
      have hp : (2 : ℕ) ^ 12 ≤ 2 ^ (12 + j.val) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      exact u.isLt.trans_le hp
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, hu]
    simp

/-- An integer mask denotes the complete preferred Q element with central coefficient zero. -/
def generatedSixthXiMaskQ (n : ℕ) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode n), 1⟩

/-- The selected scalar phase is the original full corrected Xi phase on every mask input. -/
theorem generatedSixth_xi_mask_phase (n : ℕ) :
    toAdd (spinConjugation (generatedSixthCorrectedGenerator 4).val.1
      (generatedSixthXiMaskQ n)).coeff = generatedSixthXiSelectedPhase
        (generatedSixthXiMaskQ n) :=
  generatedSixth_xi_selected_phase (generatedSixthXiMaskQ n)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
