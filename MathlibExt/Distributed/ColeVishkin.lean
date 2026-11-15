/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Distinct naturals differ at some bit position. -/
theorem exists_testBit_ne (x y : ℕ) (h : x ≠ y) :
    ∃ k, x.testBit k ≠ y.testBit k := by
  by_contra hc
  exact h (Nat.eq_of_testBit_eq fun k => of_not_not (fun hn => hc ⟨k, hn⟩))

/-- The least bit position where two distinct naturals differ. -/
noncomputable def lsbDiff (x y : ℕ) (h : x ≠ y) : ℕ :=
  Nat.find (exists_testBit_ne x y h)

/-- At the least differing bit, the bits do differ. -/
theorem testBit_lsbDiff (x y : ℕ) (h : x ≠ y) :
    x.testBit (lsbDiff x y h) ≠ y.testBit (lsbDiff x y h) :=
  Nat.find_spec (exists_testBit_ne x y h)

/-- One Cole-Vishkin step: the new color of a node holding color
`x` whose successor holds color `y` (with `x ≠ y`). -/
noncomputable def cvColor (x y : ℕ) (h : x ≠ y) : ℕ :=
  2 * lsbDiff x y h + (if x.testBit (lsbDiff x y h) then 1 else 0)

/-- One CV step is proper along a directed path: if `x ≠ y` and
`y ≠ z`, the new colors of the first two nodes differ. -/
theorem cvColor_proper (x y z : ℕ) (hxy : x ≠ y) (hyz : y ≠ z) :
    cvColor x y hxy ≠ cvColor y z hyz := by
  unfold cvColor
  intro hEq
  have hb1 : (if x.testBit (lsbDiff x y hxy) then (1 : ℕ) else 0) ≤ 1 := by
    by_cases hc : x.testBit (lsbDiff x y hxy) <;> simp [hc]
  have hb2 : (if y.testBit (lsbDiff y z hyz) then (1 : ℕ) else 0) ≤ 1 := by
    by_cases hc : y.testBit (lsbDiff y z hyz) <;> simp [hc]
  have hij : lsbDiff x y hxy = lsbDiff y z hyz := by omega
  have h1 := testBit_lsbDiff x y hxy
  rw [hij] at h1 hEq
  cases hx : x.testBit (lsbDiff y z hyz) <;> cases hy : y.testBit (lsbDiff y z hyz)
    <;> simp_all

/-- The new color is small: if `x, y < 2 ^ k` with `1 ≤ k`, then
the CV color is below `2 * k`. -/
theorem cvColor_lt (x y : ℕ) (h : x ≠ y) {k : ℕ} (hk : 1 ≤ k)
    (hx : x < 2 ^ k) (hy : y < 2 ^ k) :
    cvColor x y h < 2 * k := by
  unfold cvColor
  have hb : (if x.testBit (lsbDiff x y h) then (1 : ℕ) else 0) ≤ 1 := by
    by_cases hc : x.testBit (lsbDiff x y h) <;> simp [hc]
  have hlk : lsbDiff x y h < k := by
    by_contra hcon
    push Not at hcon
    have heq : x = y := by
      apply Nat.eq_of_testBit_eq
      intro m
      by_cases hm : m < k
      · by_contra hne
        have hle : lsbDiff x y h ≤ m := Nat.find_min' _ hne
        omega
      · push Not at hm
        have hxm : x < 2 ^ m := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hm)
        have hym : y < 2 ^ m := lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hm)
        rw [Nat.testBit_lt_two_pow hxm, Nat.testBit_lt_two_pow hym]
    exact h heq
  have hi : lsbDiff x y h ≤ k - 1 := by omega
  omega
