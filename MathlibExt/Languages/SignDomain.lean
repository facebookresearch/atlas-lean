/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Int.Basic
public import Mathlib.Algebra.Order.Ring.Basic

/-!
# Sign domain for abstract interpretation

The sign domain abstracts integers by their sign. This module
defines the domain, the abstract addition and multiplication
tables, and proves both sound: the sign of a computed result is
always among the abstractly possible signs. The IMP semantics
and the interval domain are not formalized here.
-/

@[expose] public section

/-- Signs for the sign domain (core of VER-14). -/
inductive Sign : Type
  | neg : Sign
  | zero : Sign
  | pos : Sign
deriving DecidableEq

/-- Sign of an integer. -/
def signOf (z : ℤ) : Sign :=
  if z < 0 then Sign.neg else if z = 0 then Sign.zero else Sign.pos

/-- Possible signs of a sum, as a finset of signs. -/
def addSigns : Sign → Sign → Finset Sign
  | Sign.neg, Sign.neg => {Sign.neg}
  | Sign.neg, Sign.zero => {Sign.neg}
  | Sign.neg, Sign.pos => {Sign.neg, Sign.zero, Sign.pos}
  | Sign.zero, s => {s}
  | Sign.pos, Sign.neg => {Sign.neg, Sign.zero, Sign.pos}
  | Sign.pos, Sign.zero => {Sign.pos}
  | Sign.pos, Sign.pos => {Sign.pos}

private theorem signOf_of_neg {z : ℤ} (h : z < 0) : signOf z = Sign.neg := by
  simp [signOf, h]

private theorem signOf_of_eq_zero {z : ℤ} (h : z = 0) : signOf z = Sign.zero := by
  simp [signOf, h]

private theorem signOf_of_pos {z : ℤ} (h : 0 < z) : signOf z = Sign.pos := by
  have h1 : ¬z < 0 := by omega
  have h2 : ¬z = 0 := by omega
  simp [signOf, h1, h2]

/-- Soundness of sign addition: the sign of a sum is always a
possible sign of the sum of signs. -/
theorem signOf_add_mem (a b : ℤ) :
    signOf (a + b) ∈ addSigns (signOf a) (signOf b) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [signOf_of_neg ha, signOf_of_neg hb,
        signOf_of_neg (show a + b < 0 by omega)]
      decide
    · rw [signOf_of_neg ha, signOf_of_eq_zero hb,
        signOf_of_neg (show a + b < 0 by omega)]
      decide
    · rw [signOf_of_neg ha, signOf_of_pos hb]
      rcases lt_trichotomy (a + b) 0 with hab | hab | hab
      · rw [signOf_of_neg hab]; decide
      · rw [signOf_of_eq_zero hab]; decide
      · rw [signOf_of_pos hab]; decide
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [signOf_of_eq_zero ha, signOf_of_neg hb,
        signOf_of_neg (show a + b < 0 by omega)]
      decide
    · rw [signOf_of_eq_zero ha, signOf_of_eq_zero hb,
        signOf_of_eq_zero (show a + b = 0 by omega)]
      decide
    · rw [signOf_of_eq_zero ha, signOf_of_pos hb,
        signOf_of_pos (show 0 < a + b by omega)]
      decide
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [signOf_of_pos ha, signOf_of_neg hb]
      rcases lt_trichotomy (a + b) 0 with hab | hab | hab
      · rw [signOf_of_neg hab]; decide
      · rw [signOf_of_eq_zero hab]; decide
      · rw [signOf_of_pos hab]; decide
    · rw [signOf_of_pos ha, signOf_of_eq_zero hb,
        signOf_of_pos (show 0 < a + b by omega)]
      decide
    · rw [signOf_of_pos ha, signOf_of_pos hb,
        signOf_of_pos (show 0 < a + b by omega)]
      decide

/-- Possible signs of a product. -/
def mulSigns : Sign → Sign → Finset Sign
  | Sign.zero, _ => {Sign.zero}
  | _, Sign.zero => {Sign.zero}
  | Sign.neg, Sign.neg => {Sign.pos}
  | Sign.neg, Sign.pos => {Sign.neg}
  | Sign.pos, Sign.neg => {Sign.neg}
  | Sign.pos, Sign.pos => {Sign.pos}

/-- Soundness of sign multiplication. -/
theorem signOf_mul_mem (a b : ℤ) :
    signOf (a * b) ∈ mulSigns (signOf a) (signOf b) := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [signOf_of_neg ha, signOf_of_neg hb,
        signOf_of_pos (show 0 < a * b by exact Int.mul_pos_iff.mpr (Or.inr ⟨ha, hb⟩))]
      decide
    · rw [signOf_of_neg ha, signOf_of_eq_zero hb,
        signOf_of_eq_zero (show a * b = 0 by simp [hb])]
      decide
    · rw [signOf_of_neg ha, signOf_of_pos hb,
        signOf_of_neg (show a * b < 0 by exact Int.mul_neg_iff.mpr (Or.inr ⟨ha, hb⟩))]
      decide
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [signOf_of_eq_zero ha, signOf_of_neg hb,
        signOf_of_eq_zero (show a * b = 0 by simp [ha])]
      decide
    · rw [signOf_of_eq_zero ha, signOf_of_eq_zero hb,
        signOf_of_eq_zero (show a * b = 0 by simp [ha])]
      decide
    · rw [signOf_of_eq_zero ha, signOf_of_pos hb,
        signOf_of_eq_zero (show a * b = 0 by simp [ha])]
      decide
  · rcases lt_trichotomy b 0 with hb | hb | hb
    · rw [signOf_of_pos ha, signOf_of_neg hb,
        signOf_of_neg (show a * b < 0 by exact Int.mul_neg_iff.mpr (Or.inl ⟨ha, hb⟩))]
      decide
    · rw [signOf_of_pos ha, signOf_of_eq_zero hb,
        signOf_of_eq_zero (show a * b = 0 by simp [hb])]
      decide
    · rw [signOf_of_pos ha, signOf_of_pos hb,
        signOf_of_pos (show 0 < a * b by exact Int.mul_pos_iff.mpr (Or.inl ⟨ha, hb⟩))]
      decide

end
