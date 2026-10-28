/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinPackedHighPairGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisPackedSlotPermutation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedSignedBounded

/-! Complete original low Fourier pairs as seven signed full-word terms. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The original four-bit slot after toggling one genuine low Fourier bit. -/
def generatedNinthLowerSpinPackedSlotXor (k : Fin 4) (i : Fin 16) : Fin 16 :=
  ⟨i.val ^^^ 2 ^ k.val, by
    have h : 2 ^ k.val < 16 := by
      simpa only [show 2 ^ 4 = 16 by decide] using
        Nat.pow_lt_pow_right (by decide : 1 < 2) k.isLt
    change i.val ^^^ 2 ^ k.val < 2 ^ 4
    exact Nat.xor_lt_two_pow i.isLt h⟩

/-- Seven full words retain all original positive and negative Fourier contributions. -/
def generatedNinthLowerSpinPackedLowSources (w : ℕ) (k l : Fin 4) : Fin 7 → ℕ :=
  let wl := generatedAxisPackedSlotPermuteWord 9 l.val w
  let wk := generatedAxisPackedSlotPermuteWord 9 k.val w
  ![w &&& generatedAxisPackedSlotPositionMask 9
      (fun i => !(i.testBit k.val ^^ i.testBit l.val)),
    w &&& generatedAxisPackedSlotPositionMask 9
      (fun i => i.testBit k.val ^^ i.testBit l.val),
    wl &&& generatedAxisPackedSlotPositionMask 9 (fun i => !(i.testBit k.val)),
    wl &&& generatedAxisPackedSlotPositionMask 9 (fun i => i.testBit k.val),
    wk &&& generatedAxisPackedSlotPositionMask 9 (fun i => !(i.testBit l.val)),
    wk &&& generatedAxisPackedSlotPositionMask 9 (fun i => i.testBit l.val),
    generatedAxisPackedSlotPermuteWord 9 k.val wl]

/-- Every original negative term remains a genuine integral negative coefficient. -/
def generatedNinthLowerSpinPackedLowCoefficients : Fin 7 → ℤ := ![1, -1, 1, -1, 1, -1, 1]

private theorem signed_digit_slot (w : ℕ) (i : Fin 16) :
    generatedRootEightPackedSignedDigit w i =
      if generatedAxisPackedSlotDigit 9 w i.val < 256 then
        (generatedAxisPackedSlotDigit 9 w i.val : ℤ)
      else (generatedAxisPackedSlotDigit 9 w i.val : ℤ) - 512 := by
  have hp : 512 ^ i.val = 2 ^ (9 * i.val) := by rw [pow_mul]; norm_num
  simp only [generatedRootEightPackedSignedDigit, generatedAxisPackedSlotDigit, hp,
    show (2 : ℕ) ^ 9 = 512 by decide]

/-- A complete position mask retains the exact original signed digit or gives zero. -/
theorem generatedNinth_lower_spin_packed_signed_position_mask
    (w : ℕ) (p : ℕ → Bool) (i : Fin 16) :
    generatedRootEightPackedSignedDigit (w &&& generatedAxisPackedSlotPositionMask 9 p) i =
      if p i.val = true then generatedRootEightPackedSignedDigit w i else 0 := by
  rw [signed_digit_slot, signed_digit_slot,
    generatedAxisPackedSlotPositionMask_and_digit]
  by_cases h : p i.val = true <;> simp [i.isLt, h]

/-- A whole-word low-bit permutation retains every original signed digit. -/
theorem generatedNinth_lower_spin_packed_signed_slot_permutation
    (w : ℕ) (k : Fin 4) (i : Fin 16) :
    generatedRootEightPackedSignedDigit (generatedAxisPackedSlotPermuteWord 9 k.val w) i =
      generatedRootEightPackedSignedDigit w (generatedNinthLowerSpinPackedSlotXor k i) := by
  rw [signed_digit_slot, signed_digit_slot, generatedAxisPackedSlotPermuteWord_digit]
  rfl

private theorem low_prefix_xor (k : Fin 4) (a : Fin 256) (i : Fin 16) :
    (⟨(Nat.xor (generatedNinthLowerSpinPackedPrefixIndex a i).val (2 ^ k.val)) % 4096,
      Nat.mod_lt _ (by decide)⟩ : Fin 4096) =
      generatedNinthLowerSpinPackedPrefixIndex a (generatedNinthLowerSpinPackedSlotXor k i) := by
  apply Fin.ext
  have hbit : 2 ^ k.val < 16 := by
    simpa only [show 2 ^ 4 = 16 by decide] using
      Nat.pow_lt_pow_right (by decide : 1 < 2) k.isLt
  have hdiv : (2 : ℕ) ^ k.val / 16 = 0 := Nat.div_eq_of_lt hbit
  have hmod : 2 ^ k.val % 16 = 2 ^ k.val := Nat.mod_eq_of_lt hbit
  have hn : a.val * 16 + i.val < 4096 := by omega
  have hx : Nat.xor (a.val * 16 + i.val) (2 ^ k.val) < 4096 := by
    change Nat.xor (a.val * 16 + i.val) (2 ^ k.val) < 2 ^ 12
    exact Nat.xor_lt_two_pow hn (show 2 ^ k.val < 4096 by omega)
  have ha : (a.val * 16 + i.val) / 16 = a.val := by omega
  have hi : (a.val * 16 + i.val) % 16 = i.val := by omega
  have hd := Nat.xor_div_two_pow (a := a.val * 16 + i.val) (b := 2 ^ k.val) (n := 4)
  have hm := Nat.xor_mod_two_pow (a := a.val * 16 + i.val) (b := 2 ^ k.val) (n := 4)
  change Nat.xor (a.val * 16 + i.val) (2 ^ k.val) / 16 = _ at hd
  change Nat.xor (a.val * 16 + i.val) (2 ^ k.val) % 16 = _ at hm
  rw [ha, hdiv, Nat.xor_zero] at hd
  rw [hi, hmod] at hm
  have hr := Nat.mod_add_div (Nat.xor (a.val * 16 + i.val) (2 ^ k.val)) 16
  rw [hd, hm] at hr
  dsimp only [generatedNinthLowerSpinPackedPrefixIndex, generatedNinthLowerSpinPackedSlotXor]
  rw [Nat.mod_eq_of_lt hx]
  omega

private theorem low_prefix_testBit (k : Fin 4) (a : Fin 256) (i : Fin 16) :
    (generatedNinthLowerSpinPackedPrefixIndex a i).val.testBit k.val = i.val.testBit k.val := by
  have hi : (a.val * 16 + i.val) % 16 = i.val := by omega
  have ht := Nat.testBit_mod_two_pow (a.val * 16 + i.val) 4 k.val
  change (a.val * 16 + i.val).testBit k.val = i.val.testBit k.val
  simpa only [show 2 ^ 4 = 16 by decide, hi, k.isLt, decide_true, Bool.true_and]
    using ht.symm

private theorem slot_xor_testBit (k l : Fin 4) (hkl : k ≠ l) (i : Fin 16) :
    (generatedNinthLowerSpinPackedSlotXor k i).val.testBit l.val = i.val.testBit l.val := by
  have hval : k.val ≠ l.val := by intro h; apply hkl; exact Fin.ext h
  change (i.val ^^^ 2 ^ k.val).testBit l.val = i.val.testBit l.val
  rw [Nat.testBit_xor, Nat.testBit_two_pow_of_ne hval]
  cases i.val.testBit l.val <;> rfl

private theorem low_fourier_prefix (k : Fin 4) (v : NortonUIntegerVector)
    (a : Fin 256) (i : Fin 16) :
    generatedNinthLowerSpinTensorFourierInteger ⟨k.val, by omega⟩ v
      (generatedNinthLowerSpinPackedPrefixIndex a i) =
        (if i.val.testBit k.val then (-1 : ℤ) else 1) *
          v (generatedNinthLowerSpinPackedPrefixIndex a i) +
            v (generatedNinthLowerSpinPackedPrefixIndex a
              (generatedNinthLowerSpinPackedSlotXor k i)) := by
  unfold generatedNinthLowerSpinTensorFourierInteger
  rw [low_prefix_testBit, low_prefix_xor]

/-- The complete actual low Fourier pair equals seven original signed whole-word digits. -/
theorem generatedNinth_lower_spin_packed_low_pair_expansion
    (w : Fin 16 → Fin 16 → ℕ) (k l : Fin 4) (hkl : k ≠ l)
    (a : Fin 256) (i : Fin 16) :
    generatedNinthLowerSpinTensorFourierInteger ⟨k.val, by omega⟩
      (generatedNinthLowerSpinTensorFourierInteger ⟨l.val, by omega⟩
        (generatedNinthLowerSpinTensorPackedCoordinate w))
          (generatedNinthLowerSpinPackedPrefixIndex a i) =
      ∑ z : Fin 7, generatedNinthLowerSpinPackedLowCoefficients z *
        generatedRootEightPackedSignedDigit
          (generatedNinthLowerSpinPackedLowSources
            (w ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩) k l z) i := by
  rw [low_fourier_prefix, low_fourier_prefix, low_fourier_prefix,
    slot_xor_testBit k l hkl]
  simp only [generatedNinth_lower_spin_packed_prefix_coordinate]
  simp [generatedNinthLowerSpinPackedLowSources, generatedNinthLowerSpinPackedLowCoefficients,
    Fin.sum_univ_succ, generatedNinth_lower_spin_packed_signed_position_mask,
    generatedNinth_lower_spin_packed_signed_slot_permutation]
  cases i.val.testBit k.val <;> cases i.val.testBit l.val <;> simp <;> ring

/-- Full seven-word slot equations imply all original 4096 actual Fourier coordinates. -/
theorem generatedNinth_lower_spin_packed_low_pair_of_coordinates
    (w t : Fin 16 → Fin 16 → ℕ) (k l : Fin 4) (hkl : k ≠ l)
    (h : ∀ a : Fin 256, ∀ i : Fin 16,
      (∑ z : Fin 7, generatedNinthLowerSpinPackedLowCoefficients z *
        generatedRootEightPackedSignedDigit
          (generatedNinthLowerSpinPackedLowSources
            (w ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩) k l z) i) =
        2 * generatedRootEightPackedSignedDigit
          (t ⟨a.val / 16, by omega⟩ ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩) i) :
    ∀ n : Fin 4096,
      generatedNinthLowerSpinTensorFourierInteger ⟨k.val, by omega⟩
        (generatedNinthLowerSpinTensorFourierInteger ⟨l.val, by omega⟩
          (generatedNinthLowerSpinTensorPackedCoordinate w)) n =
        2 * generatedNinthLowerSpinTensorPackedCoordinate t n := by
  intro n
  let a : Fin 256 := ⟨n.val / 16, by omega⟩
  let i : Fin 16 := ⟨n.val % 16, Nat.mod_lt _ (by decide)⟩
  have hn : generatedNinthLowerSpinPackedPrefixIndex a i = n := by
    apply Fin.ext
    dsimp [generatedNinthLowerSpinPackedPrefixIndex, a, i]
    omega
  rw [← hn, generatedNinth_lower_spin_packed_low_pair_expansion w k l hkl,
    generatedNinth_lower_spin_packed_prefix_coordinate]
  exact h a i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
