/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthXiFoldedPhase

/-! Folding original row masks before their scalar parity retains every preferred-Q phase. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency true

/-- Folded low-bit parity respects the original characteristic-two mask addition. -/
theorem generatedSixth_xi_folded_parity_xor (n m : ℕ) :
    generatedSixthXiFoldedParity (Nat.xor n m) =
      generatedSixthXiFoldedParity n + generatedSixthXiFoldedParity m := by
  simp only [generatedSixth_xi_folded_parity, generatedSixth_xi_bit_scalar_xor,
    Finset.sum_add_distrib]

/-- Accumulate the selected original ordered cocycle rows without evaluating a scalar early. -/
def generatedSixthXiFoldedRowMask (n : ℕ) (r : Fin 24 → ℕ) (c : ℕ) :
    List (Fin 24) → ℕ
  | [] => c
  | i :: l => if n.testBit i.val then
      Nat.xor (n &&& r i) (generatedSixthXiFoldedRowMask n r c l)
    else generatedSixthXiFoldedRowMask n r c l

/-- Every accumulated original row contributes precisely its selected scalar parity. -/
theorem generatedSixth_xi_folded_row_mask (n : ℕ) (r : Fin 24 → ℕ) (c : ℕ)
    (l : List (Fin 24)) :
    generatedSixthXiFoldedParity (generatedSixthXiFoldedRowMask n r c l) =
      generatedSixthXiFoldedParity c +
        (l.map (fun i => generatedSixthXiBitScalar n i.val *
          generatedSixthXiFoldedParity (n &&& r i))).sum := by
  induction l with
  | nil => simp [generatedSixthXiFoldedRowMask]
  | cons i l ih =>
    cases h : n.testBit i.val
    · simp only [generatedSixthXiFoldedRowMask, Bool.false_eq_true, ite_false,
        ih, List.map_cons, List.sum_cons, generatedSixthXiBitScalar,
        h, ite_false, zero_mul, zero_add]
    · simp only [generatedSixthXiFoldedRowMask, ite_true,
        generatedSixth_xi_folded_parity_xor, ih, List.map_cons, List.sum_cons,
        generatedSixthXiBitScalar, h, ite_true, one_mul]
      abel

/-- One final folded parity evaluates all genuine central and ordered row contributions. -/
def generatedSixthXiFoldedScalar (n : ℕ) : ZMod 2 :=
  generatedSixthXiFoldedParity (generatedSixthXiFoldedRowMask n
    generatedSixthXiUpperPairRows (n &&& generatedSixthXiCoordinateCentralMask)
    (List.finRange 24))

/-- The compact accumulated scalar equals the complete actual preferred-Q phase. -/
theorem generatedSixth_xi_folded_scalar (n : ℕ) :
    generatedSixthXiFoldedScalar n = generatedSixthXiFastMaskPhase n := by
  rw [← generatedSixth_xi_folded_phase]
  unfold generatedSixthXiFoldedScalar generatedSixthXiFoldedPhase
  have h := generatedSixth_xi_folded_row_mask n generatedSixthXiUpperPairRows
    (n &&& generatedSixthXiCoordinateCentralMask) (List.finRange 24)
  simpa only [← List.ofFn_eq_map, List.sum_ofFn] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
