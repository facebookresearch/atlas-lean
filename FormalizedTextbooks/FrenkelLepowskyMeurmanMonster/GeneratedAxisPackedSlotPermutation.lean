/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisPackedSlotPositionMasks
public import Mathlib.Tactic

/-! The low Fourier bits permute all sixteen original radix slots by exclusive disjunction. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A fixed radix value at selected original slots, for bias and sign-mask encodings. -/
def generatedAxisPackedSlotPositionValueMask (b value : ℕ) (p : ℕ → Bool) : ℕ :=
  Nat.ofDigits (2 ^ b) (List.ofFn fun i : Fin 16 => if p i.val then value else 0)

/-- Every constant position-mask digit retains its exact value or is zero. -/
theorem generatedAxisPackedSlotPositionValueMask_digit (b value i : ℕ) (p : ℕ → Bool)
    (hv : value < 2 ^ b) :
    generatedAxisPackedSlotDigit b (generatedAxisPackedSlotPositionValueMask b value p) i =
      if i < 16 ∧ p i = true then value else 0 := by
  have hL : ∀ a ∈ (List.ofFn fun j : Fin 16 => if p j.val then value else 0),
      a < 2 ^ b := by
    intro a ha
    rcases List.mem_ofFn.mp ha with ⟨j, rfl⟩
    split
    · exact hv
    · exact Nat.two_pow_pos b
  unfold generatedAxisPackedSlotDigit generatedAxisPackedSlotPositionValueMask
  rw [show 2 ^ (b * i) = (2 ^ b) ^ i by rw [pow_mul],
    generatedAxisPackedSlot_ofDigits_digit _ (Nat.two_pow_pos b) _ hL]
  change (List.ofFn (fun j : Fin 16 => if p j.val then value else 0))[i]?.getD 0 =
    if i < 16 ∧ p i = true then value else 0
  rw [List.getElem?_ofFn]
  split <;> rename_i hi
  · simp only [Option.getD_some, hi, true_and]
  · simp only [Option.getD_none, hi, false_and, ite_false]

/-- Dividing by a radix power moves every complete digit down by the stated slot count. -/
theorem generatedAxisPackedSlotDigit_div_power (b w d i : ℕ) :
    generatedAxisPackedSlotDigit b (w / 2 ^ (b * d)) i =
      generatedAxisPackedSlotDigit b w (i + d) := by
  unfold generatedAxisPackedSlotDigit
  rw [Nat.div_div_eq_div_mul, ← pow_add,
    show b * d + b * i = b * (i + d) by ring]

/-- Multiplication by a radix power shifts complete digits up and introduces only zero slots. -/
theorem generatedAxisPackedSlotDigit_mul_power (b w d i : ℕ) :
    generatedAxisPackedSlotDigit b (w * 2 ^ (b * d)) i =
      if d ≤ i then generatedAxisPackedSlotDigit b w (i - d) else 0 := by
  by_cases hd : d ≤ i
  · rw [ite_eq_left hd]
    apply Nat.eq_of_testBit_eq
    intro n
    simp only [generatedAxisPackedSlotDigit, Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow]
    have hp : b * d ≤ b * i := Nat.mul_le_mul_left b hd
    have hpn : b * d ≤ n + b * i := by omega
    have he : n + b * i - b * d = n + b * (i - d) := by
      rw [Nat.mul_sub_left_distrib]
      omega
    simp only [hpn, decide_true, Bool.true_and, he]
  · rw [ite_eq_right hd]
    apply Nat.eq_of_testBit_eq
    intro n
    simp only [generatedAxisPackedSlotDigit, Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow, Nat.zero_testBit]
    by_cases hn : n < b
    · have hi : i + 1 ≤ d := by omega
      have hp := Nat.mul_le_mul_left b hi
      have he : ¬ b * d ≤ n + b * i := by
        rw [Nat.mul_add, Nat.mul_one] at hp
        omega
      simp only [hn, he, decide_true, decide_false, Bool.false_and, Bool.true_and]
    · simp only [hn, decide_false, Bool.false_and]

/-- All bits of the original slots with the selected low bit zero. -/
def generatedAxisPackedSlotEvenMask (b k : ℕ) : ℕ :=
  generatedAxisPackedSlotPositionMask b (fun i => !(i.testBit k))

/-- All bits of the original slots with the selected low bit one. -/
def generatedAxisPackedSlotOddMask (b k : ℕ) : ℕ :=
  generatedAxisPackedSlotPositionMask b (fun i => i.testBit k)

/-- Swap both halves of every original low-bit slot block, retaining all radix bits. -/
def generatedAxisPackedSlotPermuteWord (b k w : ℕ) : ℕ :=
  ((w &&& generatedAxisPackedSlotEvenMask b k) * (2 ^ b) ^ (2 ^ k)) |||
    ((w &&& generatedAxisPackedSlotOddMask b k) / (2 ^ b) ^ (2 ^ k))

/-- Every original slot is exactly the source slot whose selected low bit was toggled.
The result holds for every natural word, so in particular for every full sixteen-slot word. -/
theorem generatedAxisPackedSlotPermuteWord_digit (b w : ℕ) (k : Fin 4) (i : Fin 16) :
    generatedAxisPackedSlotDigit b (generatedAxisPackedSlotPermuteWord b k.val w) i.val =
      generatedAxisPackedSlotDigit b w (i.val ^^^ 2 ^ k.val) := by
  fin_cases k <;> fin_cases i <;>
    simp only [generatedAxisPackedSlotPermuteWord, generatedAxisPackedSlotEvenMask,
      generatedAxisPackedSlotOddMask, ← pow_mul, generatedAxisPackedSlotDigit_or,
      generatedAxisPackedSlotDigit_mul_power, generatedAxisPackedSlotDigit_div_power,
      generatedAxisPackedSlotPositionMask_and_digit]
  all_goals norm_num [Nat.testBit]
  all_goals rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
