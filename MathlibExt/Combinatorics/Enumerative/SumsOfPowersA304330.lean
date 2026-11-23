/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted binomial sums

The sums in Cereceda's Lemmas 4 and 7 telescope by Pascal's identity and the
absorption identity for binomial coefficients.
-/

public section

namespace MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

/-- **Sum of $2i \binom{2i+k-1}{2k-1}$.** For all natural numbers $k \ge 1$ and $n \ge 1$,
$$\sum_{i=1}^{n} 2i \binom{2i + k - 1}{2k - 1} = k \binom{2n + k + 1}{2k + 1}.$$

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 4. -/
theorem sum_two_mul_choose_eq (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n,
      (2 * i) * Nat.choose (2 * i + k - 1) (2 * k - 1)) =
      k * Nat.choose (2 * n + k + 1) (2 * k + 1) := by
  let F (i : ℕ) := k * (2 * i + k + 1).choose (2 * k + 1)
  have step (i : ℕ) :
      F i + 2 * (i + 1) * (2 * (i + 1) + k - 1).choose (2 * k - 1) = F (i + 1) := by
    dsimp only [F]
    set a := 2 * i + k + 1 with ha
    have htop : 2 * (i + 1) + k = a + 1 := by omega
    have hbot : 2 * k - 1 + 1 = 2 * k := by omega
    have pascal := Nat.choose_succ_succ' a (2 * k - 1)
    have absorb := Nat.add_one_mul_choose_eq a (2 * k - 1)
    rw [hbot] at pascal absorb
    -- Expand the binomial two rows above row a, then use absorption on row a.
    rw [htop, Nat.add_sub_cancel, Nat.choose_succ_succ' (a + 1) (2 * k),
      Nat.choose_succ_succ' a (2 * k), pascal]
    rw [pascal, ← htop] at absorb
    grind only
  induction n, hn using Nat.le_induction with
  | base =>
    simpa [F, Nat.choose_eq_zero_of_lt (show k + 1 < 2 * k + 1 by omega)] using step 0
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    exact step n

/-- **Sum of $i \binom{i+k-1}{2k-1}$.** For all natural numbers $k \ge 1$ and $n \ge 1$,
$$\sum_{i=1}^{n} i \binom{i + k - 1}{2k - 1} = \frac{k(2n + 1)}{2k + 1} \binom{n + k}{2k}.$$

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 7. -/
theorem sum_mul_choose_eq (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n,
      (i : ℚ) * (Nat.choose (i + k - 1) (2 * k - 1) : ℚ)) =
      ((k : ℚ) * (2 * (n : ℚ) + 1) / (2 * (k : ℚ) + 1)) *
        (Nat.choose (n + k) (2 * k) : ℚ) := by
  let F (i : ℕ) : ℚ := (k : ℚ) * (2 * i - 1) / (2 * k + 1) *
    ((i + k - 1).choose (2 * k) : ℚ)
  have hbot : 2 * k - 1 + 1 = 2 * k := by omega
  have step (i : ℕ) :
      (i : ℚ) * ((i + k - 1).choose (2 * k - 1) : ℚ) = F (i + 1) - F i := by
    have htop : i + k - 1 + 1 = i + k := by omega
    have pascal := Nat.choose_succ_succ' (i + k - 1) (2 * k - 1)
    have absorb := Nat.add_one_mul_choose_eq (i + k - 1) (2 * k - 1)
    rw [htop, hbot] at pascal absorb
    apply_fun (Nat.cast : ℕ → ℚ) at pascal absorb
    push_cast at pascal absorb
    dsimp only [F]
    rw [show i + 1 + k - 1 = i + k by omega]
    push_cast
    field_simp
    linear_combination absorb - k * (2 * (i : ℚ) - 1) * pascal
  rw [Finset.sum_congr rfl (fun i _ ↦ step i), Finset.sum_Icc_sub hn]
  simp [F, show 2 * ((n : ℚ) + 1) - 1 = 2 * n + 1 by ring,
    Nat.choose_eq_zero_of_lt (show k < 2 * k by omega),
    show n + 1 + k - 1 = n + k by omega]

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
