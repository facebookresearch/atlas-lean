/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.List.OfFn

/-! Radix digits and position masks for complete sixteen-slot packed words. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The complete digit in slot `i` of a word with `b` bits per slot. -/
def generatedAxisPackedSlotDigit (b w i : ℕ) : ℕ :=
  w / 2 ^ (b * i) % 2 ^ b

/-- Bitwise conjunction acts separately on every complete radix digit. -/
theorem generatedAxisPackedSlotDigit_and (b x y i : ℕ) :
    generatedAxisPackedSlotDigit b (x &&& y) i =
      generatedAxisPackedSlotDigit b x i &&& generatedAxisPackedSlotDigit b y i := by
  simp only [generatedAxisPackedSlotDigit, Nat.and_div_two_pow, Nat.and_mod_two_pow]

/-- Bitwise disjunction acts separately on every complete radix digit. -/
theorem generatedAxisPackedSlotDigit_or (b x y i : ℕ) :
    generatedAxisPackedSlotDigit b (x ||| y) i =
      generatedAxisPackedSlotDigit b x i ||| generatedAxisPackedSlotDigit b y i := by
  simp only [generatedAxisPackedSlotDigit, Nat.or_div_two_pow, Nat.or_mod_two_pow]

/-- Bitwise exclusive disjunction acts separately on every complete radix digit. -/
theorem generatedAxisPackedSlotDigit_xor (b x y i : ℕ) :
    generatedAxisPackedSlotDigit b (x ^^^ y) i =
      generatedAxisPackedSlotDigit b x i ^^^ generatedAxisPackedSlotDigit b y i := by
  simp only [generatedAxisPackedSlotDigit, Nat.xor_div_two_pow, Nat.xor_mod_two_pow]

/-- Every extracted digit is strictly below its radix. -/
theorem generatedAxisPackedSlotDigit_lt (b w i : ℕ) :
    generatedAxisPackedSlotDigit b w i < 2 ^ b :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A full radix mask retains every bit of an extracted digit. -/
theorem generatedAxisPackedSlotDigit_and_full (b w i : ℕ) :
    generatedAxisPackedSlotDigit b w i &&& (2 ^ b - 1) =
      generatedAxisPackedSlotDigit b w i :=
  Nat.and_two_pow_sub_one_of_lt_two_pow (generatedAxisPackedSlotDigit_lt b w i)

/-- A finite list of genuine digits has its original digit at every natural index. -/
theorem generatedAxisPackedSlot_ofDigits_digit (B : ℕ) (hB : 0 < B)
    (L : List ℕ) (hL : ∀ a ∈ L, a < B) (i : ℕ) :
    Nat.ofDigits B L / B ^ i % B = L[i]?.getD 0 := by
  induction i generalizing L with
  | zero =>
      cases L with
      | nil => simp [Nat.ofDigits]
      | cons a L =>
          have ha := hL a List.mem_cons_self
          simp [Nat.ofDigits, Nat.add_mod, Nat.mod_eq_of_lt ha]
  | succ i ih =>
      cases L with
      | nil => simp [Nat.ofDigits]
      | cons a L =>
          rw [pow_succ', ← Nat.div_div_eq_div_mul,
            Nat.ofDigits_div_eq_ofDigits_tail hB (a :: L) hL]
          simpa only [List.tail_cons, List.getElem?_cons_succ] using
            ih L (fun a ha => hL a (List.mem_cons_of_mem _ ha))

/-- A position mask has all radix bits set precisely at selected original slots. -/
def generatedAxisPackedSlotPositionMask (b : ℕ) (p : ℕ → Bool) : ℕ :=
  Nat.ofDigits (2 ^ b) (List.ofFn fun i : Fin 16 => if p i.val then 2 ^ b - 1 else 0)

/-- Every position-mask digit is full or zero, including all absent slots. -/
theorem generatedAxisPackedSlotPositionMask_digit (b : ℕ) (p : ℕ → Bool) (i : ℕ) :
    generatedAxisPackedSlotDigit b (generatedAxisPackedSlotPositionMask b p) i =
      if i < 16 ∧ p i = true then 2 ^ b - 1 else 0 := by
  have hL : ∀ a ∈ (List.ofFn fun j : Fin 16 => if p j.val then 2 ^ b - 1 else 0),
      a < 2 ^ b := by
    intro a ha
    rcases List.mem_ofFn.mp ha with ⟨j, rfl⟩
    split <;> have hp := Nat.two_pow_pos b <;> omega
  unfold generatedAxisPackedSlotDigit generatedAxisPackedSlotPositionMask
  rw [show 2 ^ (b * i) = (2 ^ b) ^ i by rw [pow_mul],
    generatedAxisPackedSlot_ofDigits_digit _ (Nat.two_pow_pos b) _ hL]
  change (List.ofFn (fun j : Fin 16 => if p j.val then 2 ^ b - 1 else 0))[i]?.getD 0 =
    if i < 16 ∧ p i = true then 2 ^ b - 1 else 0
  rw [List.getElem?_ofFn]
  split <;> rename_i hi
  · simp only [Option.getD_some, hi, true_and]
  · simp only [Option.getD_none, hi, false_and, ite_false]

/-- Applying a position mask keeps precisely the selected full original digits. -/
theorem generatedAxisPackedSlotPositionMask_and_digit (b w i : ℕ) (p : ℕ → Bool) :
    generatedAxisPackedSlotDigit b (w &&& generatedAxisPackedSlotPositionMask b p) i =
      if i < 16 ∧ p i = true then generatedAxisPackedSlotDigit b w i else 0 := by
  rw [generatedAxisPackedSlotDigit_and, generatedAxisPackedSlotPositionMask_digit]
  split
  · exact generatedAxisPackedSlotDigit_and_full b w i
  · simp

/-- A selected full mask complements precisely the corresponding original digit bits. -/
theorem generatedAxisPackedSlotPositionMask_xor_digit (b w i : ℕ) (p : ℕ → Bool) :
    generatedAxisPackedSlotDigit b (w ^^^ generatedAxisPackedSlotPositionMask b p) i =
      if i < 16 ∧ p i = true then
        generatedAxisPackedSlotDigit b w i ^^^ (2 ^ b - 1)
      else generatedAxisPackedSlotDigit b w i := by
  rw [generatedAxisPackedSlotDigit_xor, generatedAxisPackedSlotPositionMask_digit]
  split <;> simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
