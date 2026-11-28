/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import MathlibExt.Combinatorics.Enumerative.Hypersequence
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The hyperlucas recurrence

Taking a partial sum shifts the first difference of the Lucas recurrence defect.
Pascal's identity then gives a binomial expression for the defect at each generation.

## References

* Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
  INTEGERS 24 (2024), Article A70, pp. 1–31, Theorem 2, Equation (2.2), and
  Theorem 6, Equation (2.13), <https://doi.org/10.5281/zenodo.13331499>.
* Ayhan Dil and István Mező, *A symmetric algorithm for hyperharmonic and Fibonacci numbers*,
  Applied Mathematics and Computation 206(2) (2008), 942–951, Equation (1),
  <https://doi.org/10.1016/j.amc.2008.10.013>.
-/

namespace MetaMathlibExt

private theorem hyperLucas_zero (r : ℕ) : hypersequence lucasNumber r 0 = 2 := by
  induction r with
  | zero => rfl
  | succ r ih => rw [hypersequence_succ, Finset.sum_range_one, ih]

private theorem hyperLucas_one (r : ℕ) : hypersequence lucasNumber r 1 = 2 * r + 1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [hypersequence_succ, Finset.sum_range_succ, Finset.sum_range_one, hyperLucas_zero, ih]
    omega

private theorem hyperLucas_step (r n : ℕ) :
    ((hypersequence lucasNumber (r + 1) (n + 1) : ℕ) : ℚ) =
      ((hypersequence lucasNumber (r + 1) n : ℕ) : ℚ) +
        ((hypersequence lucasNumber r (n + 1) : ℕ) : ℚ) := by
  exact_mod_cast (show hypersequence lucasNumber (r + 1) (n + 1) =
      hypersequence lucasNumber (r + 1) n + hypersequence lucasNumber r (n + 1) by
    rw [hypersequence_succ lucasNumber r (n + 1), Finset.sum_range_succ, ← hypersequence_succ])

private def lucasRecurrenceDefect (r n : ℕ) : ℚ :=
  ((hypersequence lucasNumber r (n + 2) : ℕ) : ℚ) -
    ((hypersequence lucasNumber r (n + 1) : ℕ) : ℚ) - ((hypersequence lucasNumber r n : ℕ) : ℚ)

private theorem lucasRecurrenceDefect_succ_index (r n : ℕ) :
    lucasRecurrenceDefect (r + 1) (n + 1) =
      lucasRecurrenceDefect (r + 1) n + lucasRecurrenceDefect r (n + 1) := by
  unfold lucasRecurrenceDefect
  linear_combination hyperLucas_step r (n + 2) - hyperLucas_step r (n + 1) - hyperLucas_step r n

private theorem lucasRecurrenceDefect_succ_generation_zero (r : ℕ) :
    lucasRecurrenceDefect (r + 1) 0 =
      lucasRecurrenceDefect r 0 + ((hypersequence lucasNumber r 1 : ℕ) : ℚ) := by
  unfold lucasRecurrenceDefect
  rw [hyperLucas_zero (r + 1), hyperLucas_zero r]
  linear_combination hyperLucas_step r 1

private theorem lucasRecurrenceDefect_zero_generation (n : ℕ) : lucasRecurrenceDefect 0 n = 0 := by
  change (lucasNumber (n + 2) : ℚ) - (lucasNumber (n + 1) : ℚ) - (lucasNumber n : ℚ) = 0
  rw [lucasNumber, Nat.cast_add, add_sub_cancel_left, sub_self]

private def lucasRecurrenceCoeff (r n : ℕ) : ℚ :=
  2 * ((n + r + 2).choose r : ℚ) - ((n + r + 1).choose r : ℚ)

private theorem choose_succ_succ_rat (n k : ℕ) :
    ((n + 1).choose (k + 1) : ℚ) = (n.choose k : ℚ) + (n.choose (k + 1) : ℚ) := by
  exact_mod_cast Nat.choose_succ_succ n k

private theorem lucasRecurrenceCoeff_succ_index (r n : ℕ) :
    lucasRecurrenceCoeff (r + 1) (n + 1) =
      lucasRecurrenceCoeff (r + 1) n + lucasRecurrenceCoeff r (n + 1) := by
  have h₁ : n + 1 + (r + 1) = n + r + 2 := by omega
  have h₂ : n + 1 + r = n + r + 1 := by omega
  simp only [lucasRecurrenceCoeff, h₁, h₂]
  linear_combination 2 * choose_succ_succ_rat (n + r + 3) r -
    choose_succ_succ_rat (n + r + 2) r

private theorem lucasRecurrenceCoeff_succ_generation_zero (r : ℕ) :
    lucasRecurrenceCoeff (r + 1) 0 =
      lucasRecurrenceCoeff r 0 + ((2 * (r + 1) + 1 : ℕ) : ℚ) := by
  simp only [lucasRecurrenceCoeff, Nat.zero_add, choose_succ_succ_rat (r + 2) r,
    Nat.choose_succ_self_right]
  push_cast
  ring

private theorem lucasRecurrenceDefect_eq_coeff (r n : ℕ) :
    lucasRecurrenceDefect (r + 1) n = lucasRecurrenceCoeff r n := by
  induction r generalizing n with
  | zero =>
    induction n with
    | zero =>
      norm_num [lucasRecurrenceDefect, lucasRecurrenceCoeff, hypersequence, Finset.sum_range_succ,
        lucasNumber]
    | succ n ih =>
      rw [lucasRecurrenceDefect_succ_index, lucasRecurrenceDefect_zero_generation, add_zero, ih]
      simp [lucasRecurrenceCoeff]
  | succ r ihr =>
    induction n with
    | zero =>
      rw [lucasRecurrenceDefect_succ_generation_zero, lucasRecurrenceCoeff_succ_generation_zero,
        ihr, hyperLucas_one]
    | succ n ihn =>
      rw [lucasRecurrenceDefect_succ_index, lucasRecurrenceCoeff_succ_index, ihr, ihn]

/-- **Recurrence for the hyperlucas numbers.** Let $L^{(r)}_n$ denote the hyperlucas numbers,
the hypersequence of generation $r$ of the Lucas numbers. For all natural numbers $r$ and $n$,
$L^{(r)}_0 = 2$, $L^{(r)}_1 = 2r + 1$, and, in the rational numbers,
$$L^{(r+1)}_{n+2} = L^{(r+1)}_{n+1} + L^{(r+1)}_n + \frac{n + 2(r+1)}{n+2} \binom{n+r+1}{r}.$$

Equivalently, for $r \ge 1$,
$$L^{(r)}_{n+2} = L^{(r)}_{n+1} + L^{(r)}_n + \frac{n+2r}{n+2} \binom{n+r}{r-1}.$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 6, Equation (2.13) (`integers-2024-A70-thm-6`). -/
public theorem hyperLucas_recurrence (r n : ℕ) :
    hypersequence lucasNumber r 0 = 2 ∧ hypersequence lucasNumber r 1 = 2 * r + 1 ∧
      ((hypersequence lucasNumber (r + 1) (n + 2) : ℕ) : ℚ) =
        ((hypersequence lucasNumber (r + 1) (n + 1) : ℕ) : ℚ) +
          ((hypersequence lucasNumber (r + 1) n : ℕ) : ℚ) +
          ((n + 2 * (r + 1) : ℕ) : ℚ) / (n + 2) * ((n + r + 1).choose r : ℚ) := by
  refine ⟨hyperLucas_zero r, hyperLucas_one r, ?_⟩
  have hchoose := Nat.choose_mul_succ_eq (n + r + 1) r
  rw [show n + r + 1 + 1 - r = n + 2 by omega] at hchoose
  have hchooseRat : ((n + r + 1).choose r : ℚ) * ((n : ℚ) + r + 2) =
      ((n + r + 2).choose r : ℚ) * ((n : ℚ) + 2) := by
    exact_mod_cast hchoose
  have hden : (n : ℚ) + 2 ≠ 0 := by positivity
  have hcoeff : lucasRecurrenceCoeff r n =
      ((n + 2 * (r + 1) : ℕ) : ℚ) / (n + 2) * ((n + r + 1).choose r : ℚ) := by
    rw [div_mul_eq_mul_div, eq_div_iff hden]
    unfold lucasRecurrenceCoeff
    push_cast
    linear_combination -2 * hchooseRat
  have h := (lucasRecurrenceDefect_eq_coeff r n).trans hcoeff
  unfold lucasRecurrenceDefect at h
  linear_combination h

end MetaMathlibExt
