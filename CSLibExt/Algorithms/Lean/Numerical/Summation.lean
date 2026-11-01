/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Numerical.FloatingPoint
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Rounded summation error bound

Sequential rounded summation over `ℝ`: each partial sum is rounded
with `fl p` (round to nearest, ties to even, `p`-bit significand).
The computed sum's error against the exact sum is at most
`((1 + u)^n - 1) * ∑ |xᵢ|`, with unit roundoff `u = 2^(-p)`
(Higham, *Accuracy and Stability*, Chapter 4: the same bound holds
for any order, since the proof only uses the per-step relative
error bound `abs_fl_sub_le`).

The two parts are proved together by induction: the error bound
and the magnitude bound `|rsum| ≤ (1 + u)^n * ∑ |xᵢ|`, which the
error step needs to bound the next rounding error.
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.Algorithms.Lean.Numerical.Summation

open Cslib.Algorithms.Lean.FloatingPoint

/-- The unit roundoff of a `p`-bit significand. -/
noncomputable def unitRoundoff (p : ℕ) : ℝ := 2 ^ (-(p : ℤ))

/-- Sequential rounded summation: `fl p` on each partial sum. -/
def rsum (p : ℕ) : List ℝ → ℝ
  | [] => 0
  | x :: xs => fl p (x + rsum p xs)

/-- Error and magnitude bounds for rounded summation, together. -/
theorem rsum_bound (p : ℕ) (xs : List ℝ) :
    |rsum p xs - xs.sum| ≤
        ((1 + unitRoundoff p) ^ xs.length - 1) *
          ((xs.map fun a => |a|).sum) ∧
      |rsum p xs| ≤
        (1 + unitRoundoff p) ^ xs.length * ((xs.map fun a => |a|).sum) := by
  induction xs with
  | nil =>
      constructor <;> simp [rsum]
  | cons x xs ih =>
      obtain ⟨ih_err, ih_mag⟩ := ih
      set u := unitRoundoff p with hu
      have hu0 : 0 ≤ u := by
        rw [hu]; exact zpow_nonneg (by norm_num) _
      have hu1 : (1 : ℝ) ≤ 1 + u := by linarith
      have hpow : (1 + u) ^ (xs.length + 1) =
          (1 + u) ^ xs.length * (1 + u) := pow_succ _ _
      have hC : u ≤ (1 + u) ^ (xs.length + 1) - 1 := by
        have hle : (1 : ℝ) + u ≤ (1 + u) ^ (xs.length + 1) :=
          le_self_pow₀ hu1 (Nat.succ_ne_zero _)
        linarith
      have hfl : |fl p (x + rsum p xs) - (x + rsum p xs)| ≤
          u * |x + rsum p xs| := abs_fl_sub_le _
      have htri : |x + rsum p xs| ≤ |x| + |rsum p xs| := abs_add _ _
      have htri2 : |x + rsum p xs| ≤
          |x| + (1 + u) ^ xs.length * ((xs.map fun a => |a|).sum) :=
        le_trans htri (add_le_add_left ih_mag _)
      have hsplit : |fl p (x + rsum p xs) - (x + xs.sum)| ≤
          u * |x + rsum p xs| + |rsum p xs - xs.sum| := by
        have heq : fl p (x + rsum p xs) - (x + xs.sum) =
            (fl p (x + rsum p xs) - (x + rsum p xs)) +
              (rsum p xs - xs.sum) := by ring
        rw [heq]
        exact (abs_add _ _).trans (add_le_add hfl le_rfl)
      have hkey : u * |x + rsum p xs| + |rsum p xs - xs.sum| ≤
          u * |x| + ((1 + u) ^ (xs.length + 1) - 1) *
            ((xs.map fun a => |a|).sum) := by
        have h1 : u * |x + rsum p xs| ≤
            u * (|x| + (1 + u) ^ xs.length * ((xs.map fun a => |a|).sum)) :=
          mul_le_mul_of_nonneg_left htri2 hu0
        have h2 : |rsum p xs - xs.sum| ≤
            ((1 + u) ^ xs.length - 1) * ((xs.map fun a => |a|).sum) := ih_err
        have h3 : u * (|x| + (1 + u) ^ xs.length *
            ((xs.map fun a => |a|).sum)) +
            ((1 + u) ^ xs.length - 1) * ((xs.map fun a => |a|).sum) =
            u * |x| + ((1 + u) ^ (xs.length + 1) - 1) *
              ((xs.map fun a => |a|).sum) := by
          rw [hpow]; ring
        exact (add_le_add h1 h2).trans (le_of_eq h3)
      have hfinal : u * |x| + ((1 + u) ^ (xs.length + 1) - 1) *
          ((xs.map fun a => |a|).sum) ≤
          ((1 + u) ^ (xs.length + 1) - 1) *
            (|x| + ((xs.map fun a => |a|).sum)) := by
        have h1 : u * |x| ≤ ((1 + u) ^ (xs.length + 1) - 1) * |x| :=
          mul_le_mul_of_nonneg_right hC (abs_nonneg _)
        linarith
      have hmag : |fl p (x + rsum p xs)| ≤
          (1 + u) ^ (xs.length + 1) *
            (|x| + ((xs.map fun a => |a|).sum)) := by
        have h1 : |fl p (x + rsum p xs)| ≤
            |x + rsum p xs| + u * |x + rsum p xs| := by
          have h2 : |fl p (x + rsum p xs)| ≤
              |x + rsum p xs| + |fl p (x + rsum p xs) - (x + rsum p xs)| := by
            have htri := abs_add (x + rsum p xs)
              (fl p (x + rsum p xs) - (x + rsum p xs))
            have heq : (x + rsum p xs) +
                (fl p (x + rsum p xs) - (x + rsum p xs)) =
                fl p (x + rsum p xs) := by ring
            rw [heq] at htri
            exact htri
          exact h2.trans (add_le_add_left hfl _)
        have h2 : |x + rsum p xs| + u * |x + rsum p xs| =
            (1 + u) * |x + rsum p xs| := by ring
        have h3 : (1 + u) * |x + rsum p xs| ≤
            (1 + u) * (|x| + (1 + u) ^ xs.length *
              ((xs.map fun a => |a|).sum)) :=
          mul_le_mul_of_nonneg_left htri2 (by linarith)
        have h4 : (1 + u) * (|x| + (1 + u) ^ xs.length *
            ((xs.map fun a => |a|).sum)) =
            (1 + u) * |x| + (1 + u) ^ (xs.length + 1) *
              ((xs.map fun a => |a|).sum) := by
          rw [hpow]; ring
        have h5 : (1 + u) * |x| ≤ (1 + u) ^ (xs.length + 1) * |x| :=
          mul_le_mul_of_nonneg_right
            (le_self_pow₀ hu1 (Nat.succ_ne_zero _)) (abs_nonneg _)
        linarith
      have heq1 : rsum p (x :: xs) - (x :: xs).sum =
          fl p (x + rsum p xs) - (x + xs.sum) := by
        simp [rsum]
      have heq2 : ((x :: xs).map fun a => |a|).sum =
          |x| + ((xs.map fun a => |a|).sum) := by
        simp
      have heq3 : (x :: xs).length = xs.length + 1 := rfl
      constructor
      · rw [heq1, heq2, heq3]
        exact hsplit.trans (hkey.trans hfinal)
      · rw [show rsum p (x :: xs) = fl p (x + rsum p xs) from rfl,
          heq2, heq3]
        exact hmag

/-- The error bound alone: `|rsum - exact| ≤ ((1 + u)^n - 1) * ∑ |xᵢ|`. -/
theorem rsum_abs_sub_le (p : ℕ) (xs : List ℝ) :
    |rsum p xs - xs.sum| ≤
      ((1 + unitRoundoff p) ^ xs.length - 1) *
        ((xs.map fun a => |a|).sum) :=
  (rsum_bound p xs).1

end CSLibExt.Algorithms.Lean.Numerical.Summation
