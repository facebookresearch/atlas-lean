/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual octad spin phases and the complete local even-subset character dictionary. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadXYZFourier
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPairQProducts

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem binary_boolean_one (x : ZMod 2) :
    golayBooleanCast (decide (x = 1)) = x := by
  fin_cases x <;> decide +kernel

private theorem binary_sum_bits (e : Fin 64) :
    (∑ k : Fin 8, trialityBinaryBit e k) = 0 := by
  have h := trialityEvenMask_even e
  have hc : ((trialityBitWeight8 (trialityEvenMask e) : ℕ) : ZMod 2) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr h
  simpa only [trialityBitWeight8, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, trialityBinaryBit, golayBooleanCast] using hc

/-- Every even local physical word defines one of the actual 64 Fourier characters. -/
theorem trialityEvenCharacter_complete (v : Fin 8 → ZMod 2) (hv : ∑ k, v k = 0) :
    ∃ c : Fin 64, ∀ e : Fin 64,
      qSign (∑ k, trialityBinaryBit e k * v k) = (trialityHadamard c e : ℝ) := by
  let b : Fin 8 → Bool := fun k => decide (v k + v 7 = 1)
  have hb : ∀ k, golayBooleanCast (b k) = v k + v 7 := fun k => binary_boolean_one _
  have hb7 : b 7 = false := by simp [b, ZModModule.add_self]
  have hsum : (∑ k, golayBooleanCast (b k)) = 0 := by
    simp_rw [hb]
    rw [Finset.sum_add_distrib, hv]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    change (0 : ZMod 2) + (8 : ZMod 2) * v 7 = 0
    rw [show (8 : ZMod 2) = 0 by decide +kernel, zero_mul, zero_add]
  have hnat : 2 ∣ (∑ k, if b k then (1 : ℕ) else 0) := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      golayBooleanCast] using hsum
  obtain ⟨c,hc⟩ := trialityEvenMask_complete b hb7 hnat
  refine ⟨c, fun e => ?_⟩
  have hbit : ∀ k, trialityBinaryBit c k = v k + v 7 := by
    intro k
    simpa only [trialityBinaryBit, hc k] using hb k
  have hp : trialityBinaryPair c e = ∑ k, trialityBinaryBit e k * v k := by
    simp only [trialityBinaryPair, hbit, add_mul, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, binary_sum_bits, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [← hp, trialityHadamard_binary]
  by_cases h : trialityBinaryPair c e = 0 <;>
    simp [qSign, trialityIntegerSign, h]

theorem trialityYSpin_add_smul_omega (d : Fin 2048) (i : Fin 24)
    (t : SpinIndex) (c : ZMod 2) :
    trialityYSpin d i (t + c • trialitySpinOmega) =
      qSign c * trialityYSpin d i t := by
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide +kernel) c with rfl | rfl
  · simp only [zero_smul, add_zero, qSign_zero, one_mul]
  · simp only [one_smul, trialityYSpin_omega, qSign_one, neg_one_mul]

theorem trialityZSpin_add_smul_omega (d : Fin 2048)
    (t : SpinIndex) (c : ZMod 2) :
    trialityZSpin d (t + c • trialitySpinOmega) = trialityZSpin d t := by
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide +kernel) c with rfl | rfl
  · simp only [zero_smul, add_zero]
  · simp only [one_smul, trialityZSpin_omega]

/-- Separate the actual signed-octad Y-spin action into its source theta,
physical negative-set character, and all-one correction. -/
theorem spinOperator_octad_Y_factor (o : Fin 759) (e : Fin 64)
    (d : Fin 2048) (i : Fin 24) (t : SpinIndex) :
    spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e)))) (trialityYSpin d i) t =
      qSign (spinDot (sourceWordTheta (golayOctadLabel o)) t) *
      qSign (spinDot (golaySyndrome (integerParity (griessOctadNegativeInteger o e))) t) *
      qSign (griessOctadOmegaCoefficient e) *
        trialityYSpin d i (t + golayLabelCoefficients (golayOctadLabel o)) := by
  rw [spinOperator_griessOctad, spinDot_add_left, qSign_add]
  have ht : t + (golayLabelCoefficients (golayOctadLabel o) +
      griessOctadOmegaCoefficient e • Pi.single 11 1) =
      (t + golayLabelCoefficients (golayOctadLabel o)) +
        griessOctadOmegaCoefficient e • trialitySpinOmega := by
    unfold trialitySpinOmega
    abel
  rw [ht, trialityYSpin_add_smul_omega]
  ring

/-- The actual Z-spin action has no all-one correction sign. -/
theorem spinOperator_octad_Z_factor (o : Fin 759) (e : Fin 64)
    (d : Fin 2048) (t : SpinIndex) :
    spinOperator (griessShortQ (Sum.inr (Sum.inl (o,e)))) (trialityZSpin d) t =
      qSign (spinDot (sourceWordTheta (golayOctadLabel o)) t) *
      qSign (spinDot (golaySyndrome (integerParity (griessOctadNegativeInteger o e))) t) *
        trialityZSpin d (t + golayLabelCoefficients (golayOctadLabel o)) := by
  rw [spinOperator_griessOctad, spinDot_add_left, qSign_add]
  have ht : t + (golayLabelCoefficients (golayOctadLabel o) +
      griessOctadOmegaCoefficient e • Pi.single 11 1) =
      (t + golayLabelCoefficients (golayOctadLabel o)) +
        griessOctadOmegaCoefficient e • trialitySpinOmega := by
    unfold trialitySpinOmega
    abel
  rw [ht, trialityZSpin_add_smul_omega]

/-- Sums supported on an octad are sums over its eight actual physical coordinates. -/
theorem octad_sum_supported {R : Type*} [AddCommMonoid R] (o : Fin 759)
    (F : Fin 24 → R)
    (hF : ∀ i, (golayEncodedMask (golayOctadLabel o).val).testBit i.val = false → F i = 0) :
    (∑ i, F i) = ∑ k : Fin 8, F (golayOctadCoordinate o k) := by
  have hi : (Finset.univ.image (golayOctadCoordinate o) : Finset (Fin 24)) ⊆
      Finset.univ := Finset.subset_univ _
  have hs := Finset.sum_subset hi (fun i _ hn => show F i = 0 from by
    apply hF i
    cases h : (golayEncodedMask (golayOctadLabel o).val).testBit i.val
    · rfl
    · obtain ⟨k,hk⟩ := golayOctadCoordinate_surjective o i h
      exact False.elim (hn (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)))
  rw [← hs, Finset.sum_image]
  intro a _ b _ hab
  exact golayOctadCoordinate_injective o hab

/-- The physical syndrome character is exactly the local eight-bit dot character. -/
theorem griessOctadNegative_character_local (o : Fin 759) (e : Fin 64) (t : SpinIndex) :
    spinDot (golaySyndrome (integerParity (griessOctadNegativeInteger o e))) t =
      ∑ k : Fin 8, trialityBinaryBit e k * golayEncoder t (golayOctadCoordinate o k) := by
  rw [golaySyndrome_spinDot]
  rw [octad_sum_supported o]
  · apply Finset.sum_congr rfl
    intro k _
    rw [griessOctadNegative_local]
    rfl
  · intro i hi
    simp only [integerParity]
    have hn : (griessOctadSignMask o e).testBit i.val = false := by
      cases hs : (griessOctadSignMask o e).testBit i.val
      · rfl
      · obtain ⟨k,_,hk⟩ := (griessOctadSignMask_testBit o e i).mp hs
        have hm := golayOctadCoordinate_mem o k
        rw [hk, hi] at hm
        contradiction
    simp [griessOctadNegativeInteger, hn]

/-- Restricting any actual Golay codeword to an octad gives an even local word. -/
theorem golayEncoder_octad_restriction_even (o : Fin 759) (t : SpinIndex) :
    (∑ k : Fin 8, golayEncoder t (golayOctadCoordinate o k)) = 0 := by
  have hc : spinDot (golaySyndrome (golayEncoder t))
      (golayLabelCoefficients (golayOctadLabel o)) = 0 := by
    rw [golaySyndrome_encoder]
    simp [spinDot]
  rw [golaySyndrome_spinDot] at hc
  have hm (i : Fin 24) : golayEncoder (golayLabelCoefficients (golayOctadLabel o)) i =
      if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then 1 else 0 := by
    apply ZMod.val_injective
    cases hb : (golayEncodedMask (golayOctadLabel o).val).testBit i.val <;>
      simpa [hb, show (1 : ZMod 2).val = 1 by decide] using
        golayLabelEncoder_match (golayOctadLabel o) i
  rw [octad_sum_supported o] at hc
  · simpa only [hm, golayOctadCoordinate_mem, ite_true, mul_one] using hc
  · intro i hi
    simp only [hm, hi, Bool.false_eq_true, ite_false, mul_zero]

/-- Each actual negative-set syndrome character is an actual local Hadamard row. -/
theorem griessOctadNegative_character_Hadamard (o : Fin 759) (t : SpinIndex) :
    ∃ c : Fin 64, ∀ e : Fin 64,
      qSign (spinDot (golaySyndrome (integerParity (griessOctadNegativeInteger o e))) t) =
        (trialityHadamard c e : ℝ) := by
  obtain ⟨c,hc⟩ := trialityEvenCharacter_complete
    (fun k => golayEncoder t (golayOctadCoordinate o k))
    (golayEncoder_octad_restriction_even o t)
  refine ⟨c, fun e => ?_⟩
  rw [griessOctadNegative_character_local]
  exact hc e

/-- The actual all-one spin correction is exactly the local Fourier quadratic diagonal. -/
theorem griessOctadOmegaCoefficient_sign (e : Fin 64) :
    qSign (griessOctadOmegaCoefficient e) = (trialityIntegerDiagonal e : ℝ) := by
  unfold qSign griessOctadOmegaCoefficient trialityIntegerDiagonal
  simp only [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  split_ifs <;> norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
