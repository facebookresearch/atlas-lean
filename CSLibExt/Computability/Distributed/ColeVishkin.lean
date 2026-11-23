/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Notation

/-!
# One Cole–Vishkin color-reduction step

Cole and Vishkin's deterministic coin tossing recolors a directed path whose
adjacent nodes carry distinct colors. Colors are natural numbers read in
binary, with bit `0` the least significant. A node of color `x` compares its
color with the color `y` of its successor, the next node along the path; with
`i` the least bit position where `x` and `y` differ, its new color is
`2 * i + b`, where `b` is bit `i` of its own color `x`.

This file proves the two facts behind one round: the new coloring is again
proper along the path (`cvColor_proper`), and colors below `2 ^ k` become
colors below `2 * k` (`cvColor_lt`). Both are stated for the colors `x, y, z`
of three consecutive nodes, so they also cover the convention in which each
node compares with its predecessor: apply them to the reversed path. Iterating
the step (the `log*` round bound) and the final reduction from six to three
colors are not covered.

The color step is computable: `lsbDiff` finds the least differing bit by
halving both colors until their low bits differ.

## Main results

* `Cslib.Distributed.ColeVishkin.lsbDiff`: the least bit position where two
  distinct naturals differ.
* `Cslib.Distributed.ColeVishkin.cvColor`: the new color of one node.
* `Cslib.Distributed.ColeVishkin.cvColor_proper`: one step keeps the path
  coloring proper.
* `Cslib.Distributed.ColeVishkin.cvColor_lt`: colors below `2 ^ k` step to
  colors below `2 * k`.

## References

* R. Cole and U. Vishkin, *Deterministic coin tossing with applications to
  optimal parallel list ranking*, Information and Control 70(1), 1986,
  pp. 32–53.
-/

@[expose] public section

namespace Cslib.Distributed.ColeVishkin

/-- Distinct naturals differ at some bit position. -/
theorem exists_testBit_ne (x y : ℕ) (h : x ≠ y) :
    ∃ k, x.testBit k ≠ y.testBit k :=
  Classical.byContradiction fun hc =>
    h (Nat.eq_of_testBit_eq fun k => Classical.byContradiction fun hn => hc ⟨k, hn⟩)

/-- The least bit position where `x` and `y` differ, searching at most `fuel`
positions by halving both numbers; it returns `fuel` when the low `fuel` bits
agree. -/
def lsbDiffAux : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, x, y =>
      if x.testBit 0 = y.testBit 0 then lsbDiffAux fuel (x / 2) (y / 2) + 1 else 0

/-- With enough fuel, `lsbDiffAux` returns the least bit position where two
distinct naturals differ. -/
private theorem lsbDiffAux_spec :
    ∀ fuel x y : ℕ, x ≠ y → x + y ≤ fuel →
      x.testBit (lsbDiffAux fuel x y) ≠ y.testBit (lsbDiffAux fuel x y) ∧
        ∀ i < lsbDiffAux fuel x y, x.testBit i = y.testBit i := by
  intro fuel
  induction fuel with
  | zero =>
      intro x y hxy hle
      exact absurd (by omega : x = y) hxy
  | succ fuel ih =>
      intro x y hxy hle
      by_cases hb : x.testBit 0 = y.testBit 0
      · have hhalf : x / 2 ≠ y / 2 := by
          intro hq
          apply hxy
          apply Nat.eq_of_testBit_eq
          intro i
          cases i with
          | zero => exact hb
          | succ j => rw [Nat.testBit_succ, Nat.testBit_succ, hq]
        obtain ⟨hne, hlow⟩ := ih (x / 2) (y / 2) hhalf (by omega)
        simp only [lsbDiffAux, hb, ite_true]
        refine ⟨?_, ?_⟩
        · rw [Nat.testBit_succ, Nat.testBit_succ]
          exact hne
        · intro i hi
          cases i with
          | zero => exact hb
          | succ j =>
              rw [Nat.testBit_succ, Nat.testBit_succ]
              exact hlow j (by omega)
      · simp only [lsbDiffAux, hb, ite_false]
        exact ⟨hb, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

/-- The least bit position where two distinct naturals differ. -/
def lsbDiff (x y : ℕ) (_h : x ≠ y) : ℕ :=
  lsbDiffAux (x + y) x y

/-- At the least differing bit, the bits do differ. -/
theorem testBit_lsbDiff (x y : ℕ) (h : x ≠ y) :
    x.testBit (lsbDiff x y h) ≠ y.testBit (lsbDiff x y h) :=
  (lsbDiffAux_spec (x + y) x y h (Nat.le_refl _)).1

/-- Below the least differing bit, the bits agree. -/
theorem testBit_eq_of_lt_lsbDiff (x y : ℕ) (h : x ≠ y) {i : ℕ}
    (hi : i < lsbDiff x y h) : x.testBit i = y.testBit i :=
  (lsbDiffAux_spec (x + y) x y h (Nat.le_refl _)).2 i hi

/-- One Cole-Vishkin step: the new color of a node holding color
`x` whose successor holds color `y` (with `x ≠ y`). -/
def cvColor (x y : ℕ) (h : x ≠ y) : ℕ :=
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
    refine Nat.lt_of_not_le fun hcon => h ?_
    apply Nat.eq_of_testBit_eq
    intro m
    by_cases hm : m < k
    · exact testBit_eq_of_lt_lsbDiff x y h (by omega)
    · have hkm : k ≤ m := Nat.le_of_not_lt hm
      have hxm : x < 2 ^ m := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hkm)
      have hym : y < 2 ^ m := Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by omega) hkm)
      rw [Nat.testBit_lt_two_pow hxm, Nat.testBit_lt_two_pow hym]
  have hi : lsbDiff x y h ≤ k - 1 := by omega
  omega

end Cslib.Distributed.ColeVishkin
