/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring

/-!
# Generalized hockey stick identity

We prove the Big Hockey Stick and Pucks Identity from Lynch and Weselcouch's paper by applying
Pascal's rule twice and telescoping the resulting alternating sum.
-/

namespace MathlibExt.Combinatorics.HockeyStickWanted

open Finset

-- Taking the complementary lower index makes all terms past the cutoff vanish.
private def signedChoose (a b i : ℕ) : ℤ :=
  (-1 : ℤ) ^ i * ((a - i).choose (b + i) : ℤ)

private lemma signedChoose_eq_zero {a b i : ℕ} (h : a - i < b + i) :
    signedChoose a b i = 0 := by
  simp [signedChoose, Nat.choose_eq_zero_of_lt h]

-- Two applications of Pascal's rule express the change as a telescoping difference.
private lemma signedChoose_step (a b i : ℕ) (hi : i ≤ a) :
    signedChoose (a + 2) (b + 1) i = signedChoose a b i +
      (signedChoose (a + 1) b i - signedChoose (a + 1) b (i + 1)) := by
  simp only [signedChoose, show a + 2 - i = (a - i) + 1 + 1 by omega,
    show a + 1 - i = (a - i) + 1 by omega, Nat.add_sub_add_right,
    show b + 1 + i = (b + i) + 1 by omega, ← Nat.add_assoc,
    Nat.choose_succ_succ', Nat.cast_add, pow_succ]
  ring

private lemma sum_signedChoose (n k : ℕ) :
    ∑ i ∈ range (k + 1), ((2 * i + n).choose i : ℤ) =
      ∑ i ∈ range (k + 1), signedChoose (2 * k + 1 + n) (k + 1 + n) i := by
  induction k with
  | zero => simp [signedChoose]
  | succ k ih =>
    let a := 2 * k + 1 + n
    let b := k + 1 + n
    have hstep : ∀ i ∈ range (k + 1), signedChoose (a + 2) (b + 1) i =
        signedChoose a b i + (signedChoose (a + 1) b i - signedChoose (a + 1) b (i + 1)) :=
      fun i hi => signedChoose_step a b i (by have := mem_range.mp hi; dsimp [a]; omega)
    have hlast : signedChoose (a + 2) (b + 1) (k + 1) = 0 :=
      signedChoose_eq_zero (by dsimp [a, b]; omega)
    have hend : signedChoose (a + 1) b (k + 1) = 0 :=
      signedChoose_eq_zero (by dsimp [a, b]; omega)
    have hfirst : signedChoose (a + 1) b 0 = ((2 * (k + 1) + n).choose (k + 1) : ℤ) := by
      simp only [signedChoose, pow_zero, one_mul, Nat.sub_zero, Nat.add_zero]
      rw [show a + 1 = 2 * (k + 1) + n by dsimp [a]; omega,
        Nat.choose_symm_of_eq_add (show 2 * (k + 1) + n = b + (k + 1) by dsimp [b]; omega)]
    rw [show 2 * (k + 1) + 1 + n = a + 2 by dsimp [a]; omega,
      show k + 1 + 1 + n = b + 1 by dsimp [b]; omega,
      sum_range_succ, sum_range_succ (signedChoose _ _), hlast, add_zero,
      sum_congr rfl hstep, sum_add_distrib, sum_range_sub', hend, sub_zero, hfirst, ih]

/-- **Generalized hockey stick identity of Lynch and Weselcouch.** For all natural numbers
$n$ and $k$,
$$\sum_{i=0}^{k} \binom{2i + n}{i} =
\sum_{i=0}^{\lfloor k/2 \rfloor} (-1)^i \binom{2k + 1 + n - i}{k - 2i}.$$

Source: Molly Lynch and Michael Weselcouch, "A
Generalized Hockey Stick Theorem", Corollary 15. -/
public theorem sum_choose_two_mul_add (n k : ℕ) :
    (∑ i ∈ Finset.range (k + 1),
        (Nat.choose (2 * i + n) i : ℤ)) =
      ∑ i ∈ Finset.range (k / 2 + 1),
        (-1 : ℤ) ^ i *
          (Nat.choose (2 * k + 1 + n - i) (k - 2 * i) : ℤ) := by
  rw [sum_signedChoose]
  calc
    _ = ∑ i ∈ range (k / 2 + 1), signedChoose (2 * k + 1 + n) (k + 1 + n) i := by
      symm
      apply sum_subset (range_mono (by omega))
      intro i _ hi
      simp only [mem_range, not_lt] at hi
      exact signedChoose_eq_zero (by omega)
    _ = _ := by
      apply sum_congr rfl
      intro i hi
      have := mem_range.mp hi
      rw [signedChoose, Nat.choose_symm_of_eq_add
        (show 2 * k + 1 + n - i = (k + 1 + n + i) + (k - 2 * i) by omega)]

end MathlibExt.Combinatorics.HockeyStickWanted
