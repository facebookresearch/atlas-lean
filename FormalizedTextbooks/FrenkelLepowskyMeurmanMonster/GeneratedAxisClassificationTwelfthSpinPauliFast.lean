/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinFastDot24
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! Exact byte parity evaluates the full central and modulation sign of every genuine Q element. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem sign_add (c d : ZMod 2) :
    nortonUIntegerSign (c + d) = nortonUIntegerSign c * nortonUIntegerSign d := by
  fin_cases c <;> fin_cases d <;> decide +kernel

private theorem decode_coeff (n : Fin 4096) :
    (monsterCo1GeometryBinaryMaskDecode n.val : SpinIndex) = golayLabelCoefficients n := by
  rfl

/-- The full actual modulation character is the exact cached byte intersection parity. -/
theorem generatedTwelfth_spin_pauli_dot_fast (q : Q) (n : Fin 4096) :
    (if (generatedNinthLowerSpinFastDotTwelve
      (nortonUIntegerLabel (spinModulation q)).val n.val).testBit 0 then (1 : ZMod 2) else 0) =
      spinDot (spinModulation q) (golayLabelCoefficients n) := by
  rw [generatedNinth_lower_spin_fast_dot_twelve]
  simpa only [decode_coeff, nortonUIntegerLabel_inverse, spinDot] using
    monsterCo1GeometryBinaryMaskDot_decode 12 (nortonUIntegerLabel (spinModulation q)).val n.val

/-- Every original central bit and modulation contribution is retained in the fast integral sign. -/
theorem generatedTwelfth_spin_pauli_sign_fast (q : Q) (n : Fin 4096) :
    nortonUIntegerSign (spinPhase q (golayLabelCoefficients n)) =
      nortonUIntegerSign (toAdd q.coeff) *
        (if (generatedNinthLowerSpinFastDotTwelve
          (nortonUIntegerLabel (spinModulation q)).val n.val).testBit 0 then (-1 : ℤ) else 1) := by
  unfold spinPhase
  rw [sign_add, ← generatedTwelfth_spin_pauli_dot_fast]
  cases (generatedNinthLowerSpinFastDotTwelve
      (nortonUIntegerLabel (spinModulation q)).val n.val).testBit 0 <;>
    simp [nortonUIntegerSign]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
