/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7OutsideSignRightInverse

/-! Every even outside phase twist has exactly 128 actual original Golay corrections. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- An arbitrary six-bit outside pattern is lifted using its first five coordinates. -/
def generatedTenthE7OutsidePatternLift (y : Fin 6 → ZMod 2) : golayCode :=
  generatedTenthE7OutsideSignLift (fun i => y (Fin.castAdd 1 i))

/-- The actual lift attains every coordinate of an even outside pattern. -/
theorem generatedTenth_e7_outside_pattern_lift_actual (y : Fin 6 → ZMod 2)
    (hy : ∑ i, y i = 0) (i : Fin 6) :
    (generatedTenthE7OutsidePatternLift y).val (generatedTenthE7OutsideSignCoordinates i) =
      y i := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact generatedTenth_e7_outside_sign_lift_initial _ j
  · change (generatedTenthE7OutsideSignLift (fun j => y (Fin.castAdd 1 j))).val
      (generatedTenthE7OutsideSignCoordinates 5) = y 5
    rw [generatedTenth_e7_outside_sign_lift_last]
    have h : (∑ j : Fin 5, y (Fin.castAdd 1 j)) + y 5 = 0 := by
      rw [Fin.sum_univ_castSucc] at hy
      exact hy
    have hh := eq_neg_of_add_eq_zero_left h
    simpa only [ZMod.neg_eq_self_mod_two] using hh

/-- Full original sign conditions, written using the entire six-coordinate support. -/
theorem generatedTenth_e7_two_line_sign_condition_coordinates (c : golayCode) :
    generatedTenthE7TwoLineSignCondition c ↔
      c.val 16 = c.val 21 ∧ ∀ i : Fin 6,
        c.val (generatedTenthE7OutsideSignCoordinates i) = c.val 4 := by
  simp only [generatedTenthE7TwoLineSignCondition, Fin.forall_fin_succ,
    Fin.forall_fin_zero, generatedTenthE7OutsideSignCoordinates,
    Matrix.cons_val_zero, Matrix.cons_val_succ, eq_comm]
  tauto

/-- Complete actual Golay sign conditions after the specified outside phase twist. -/
def generatedTenthE7TwistedSignCondition (y : Fin 6 → ZMod 2) (c : golayCode) : Prop :=
  c.val 16 = c.val 21 ∧ ∀ i : Fin 6,
    c.val (generatedTenthE7OutsideSignCoordinates i) + y i = c.val 4 + y 0

/-- Addition of a genuine lift identifies the entire twisted and untwisted conditions. -/
theorem generatedTenth_e7_twisted_sign_condition (y : Fin 6 → ZMod 2)
    (hy : ∑ i, y i = 0) (c : golayCode) :
    generatedTenthE7TwistedSignCondition y c ↔
      generatedTenthE7TwoLineSignCondition (c + generatedTenthE7OutsidePatternLift y) := by
  rw [generatedTenth_e7_two_line_sign_condition_coordinates]
  change _ ↔
    c.val 16 + (generatedTenthE7OutsidePatternLift y).val 16 =
      c.val 21 + (generatedTenthE7OutsidePatternLift y).val 21 ∧
    ∀ i : Fin 6,
      c.val (generatedTenthE7OutsideSignCoordinates i) +
          (generatedTenthE7OutsidePatternLift y).val (generatedTenthE7OutsideSignCoordinates i) =
        c.val 4 + (generatedTenthE7OutsidePatternLift y).val 4
  have hn : (generatedTenthE7OutsidePatternLift y).val 16 =
      (generatedTenthE7OutsidePatternLift y).val 21 :=
    generatedTenth_e7_outside_sign_lift_normal _
  have h0 := generatedTenth_e7_outside_pattern_lift_actual y hy 0
  change (generatedTenthE7OutsidePatternLift y).val 4 = y 0 at h0
  simp only [generatedTenthE7TwistedSignCondition, hn, h0,
    generatedTenth_e7_outside_pattern_lift_actual y hy, add_right_cancel_iff]

/-- Translation by an actual Golay code bijects the entire correction fibers. -/
def generatedTenthE7TwistedSignEquiv (y : Fin 6 → ZMod 2) (hy : ∑ i, y i = 0) :
    {c : golayCode // generatedTenthE7TwistedSignCondition y c} ≃
      generatedTenthE7TwoLineSigns :=
  (Equiv.addRight (generatedTenthE7OutsidePatternLift y)).subtypeEquiv
    (fun c => generatedTenth_e7_twisted_sign_condition y hy c)

/-- Every even outside phase twist has exactly 128 actual original-code corrections. -/
theorem generatedTenth_e7_twisted_sign_fiber_card (y : Fin 6 → ZMod 2)
    (hy : ∑ i, y i = 0) :
    Nat.card {c : golayCode // generatedTenthE7TwistedSignCondition y c} = 128 := by
  rw [Nat.card_congr (generatedTenthE7TwistedSignEquiv y hy)]
  exact generatedTenth_e7_two_line_signs_card

/-- Reordering the complete outside support gives an even phase difference. -/
theorem generatedTenth_e7_permutation_phase_even (s : Equiv.Perm (Fin 6))
    (a : Fin 6 → ZMod 2) : ∑ i, (a i + a (s i)) = 0 := by
  rw [Finset.sum_add_distrib, Equiv.sum_comp s a]
  exact ZModModule.add_self _

/-- Every support permutation has exactly 128 actual Golay corrections
for its complete outside sign difference. -/
theorem generatedTenth_e7_permutation_phase_fiber_card (s : Equiv.Perm (Fin 6))
    (a : Fin 6 → ZMod 2) :
    Nat.card {c : golayCode //
      generatedTenthE7TwistedSignCondition (fun i => a i + a (s i)) c} = 128 :=
  generatedTenth_e7_twisted_sign_fiber_card _
    (generatedTenth_e7_permutation_phase_even s a)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
