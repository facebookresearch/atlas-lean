/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Moments.Variance

/-!
# Second moment and variance of the binomial distribution

Mathlib computes the mean `n p` of the binomial law `Bin(n, p)`
(`ProbabilityTheory.integral_of_hasLaw_binomial`). This file computes the second factorial
moment `E[X (X - 1)] = n (n - 1) p²`, the second moment `E[X²] = n p (1 - p) + (n p)²` and the
variance `Var X = n p (1 - p)`, for the law `Bin(ℝ, n, p)` on `ℝ` and for random variables
with that law.

## Main results

* `ProbabilityTheory.integral_mul_sub_one_map_cast_binomial`: `E[X (X - 1)] = n (n - 1) p²`.
* `ProbabilityTheory.integral_sq_map_cast_binomial`: `E[X²] = n p (1 - p) + (n p)²`.
* `ProbabilityTheory.variance_id_map_cast_binomial`: `Var X = n p (1 - p)`.
* `ProbabilityTheory.integral_mul_sub_one_of_hasLaw_binomial`,
  `ProbabilityTheory.integral_sq_of_hasLaw_binomial`,
  `ProbabilityTheory.variance_of_hasLaw_binomial`: the same three formulas for a random variable
  with law `Bin(ℝ, n, p)`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. I, 3rd ed.
  (1968), ch. IX.
-/

@[expose] public section

open MeasureTheory Finset
open scoped unitInterval

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ} {n : ℕ} {p : I}

/-- `(j + 2) (j + 1) C(m + 2, j + 2) = (m + 2) (m + 1) C(m, j)`. -/
private lemma choose_add_two_mul (m j : ℕ) :
    (m + 2).choose (j + 2) * ((j + 2) * (j + 1)) = (m + 2) * (m + 1) * m.choose j := by
  have h1 := Nat.add_one_mul_choose_eq (m + 1) (j + 1)
  have h2 := Nat.add_one_mul_choose_eq m j
  calc (m + 2).choose (j + 2) * ((j + 2) * (j + 1))
      = ((m + 2).choose (j + 2) * (j + 2)) * (j + 1) := by ring
    _ = (m + 2) * ((m + 1).choose (j + 1) * (j + 1)) := by rw [← h1]; ring
    _ = (m + 2) * (m + 1) * m.choose j := by rw [← h2]; ring

/-- **Second factorial moment of the binomial law**: `E[X (X - 1)] = n (n - 1) p²`. -/
theorem integral_mul_sub_one_map_cast_binomial :
    ∫ x, x * (x - 1) ∂Bin(ℝ, n, p) = (n : ℝ) * ((n : ℝ) - 1) * (p : ℝ) ^ 2 := by
  rw [integral_map_cast_binomial, ← Nat.range_succ_eq_Iic]
  match n with
  | 0 => simp
  | 1 => simp [sum_range_succ]
  | m + 2 =>
    rw [sum_range_succ', sum_range_succ']
    simp only [smul_eq_mul, Nat.cast_zero, zero_sub, mul_neg, mul_one, neg_zero, add_zero,
      mul_zero]
    have hterm : ∀ j ∈ range (m + 1),
        ((m + 2).choose (j + 1 + 1) * (p : ℝ) ^ (j + 1 + 1) * (1 - p) ^ (m + 2 - (j + 1 + 1))) *
          (((j + 1 + 1 : ℕ) : ℝ) * (((j + 1 + 1 : ℕ) : ℝ) - 1))
        = ((m + 2 : ℕ) : ℝ) * ((m + 2 : ℕ) - 1) * (p : ℝ) ^ 2 *
          ((p : ℝ) ^ j * (1 - p) ^ (m - j) * m.choose j) := by
      intro j _
      have hc : (((m + 2).choose (j + 2) : ℕ) : ℝ) * ((j + 2) * (j + 1))
          = (m + 2) * (m + 1) * (m.choose j : ℝ) := by
        exact_mod_cast choose_add_two_mul m j
      rw [show m + 2 - (j + 1 + 1) = m - j by omega]
      push_cast
      linear_combination (p : ℝ) ^ (j + 2) * (1 - p) ^ (m - j) * hc
    rw [sum_congr rfl hterm, ← mul_sum, ← add_pow]
    simp

/-- **Second moment of the binomial law**: `E[X²] = n p (1 - p) + (n p)²`. -/
theorem integral_sq_map_cast_binomial :
    ∫ x, x ^ 2 ∂Bin(ℝ, n, p) = (n : ℝ) * p * (1 - (p : ℝ)) + ((n : ℝ) * p) ^ 2 := by
  have h : (fun x : ℝ => x ^ 2) = fun x => x * (x - 1) + x := by
    funext x
    ring
  rw [h, integral_add (integrable_map_cast_binomial _) (integrable_map_cast_binomial _),
    integral_mul_sub_one_map_cast_binomial, (integral_of_hasLaw_binomial HasLaw.id :
      ∫ x, x ∂Bin(ℝ, n, p) = (p : ℝ) * n)]
  ring

/-- **Variance of the binomial law**: `Var X = n p (1 - p)`. -/
theorem variance_id_map_cast_binomial :
    Var[id; Bin(ℝ, n, p)] = (n : ℝ) * p * (1 - (p : ℝ)) := by
  have hmem : MemLp id 2 Bin(ℝ, n, p) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
      (by simpa using integrable_map_cast_binomial (fun x : ℝ => x ^ 2))
  rw [variance_eq_sub hmem]
  simp only [id_eq, Pi.pow_apply]
  rw [integral_sq_map_cast_binomial, (integral_of_hasLaw_binomial HasLaw.id :
      ∫ x, x ∂Bin(ℝ, n, p) = (p : ℝ) * n)]
  ring

/-- **Second factorial moment of a binomial random variable**: if `X` has law `Bin(ℝ, n, p)`
then `E[X (X - 1)] = n (n - 1) p²`. -/
theorem integral_mul_sub_one_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) :
    P[fun ω => X ω * (X ω - 1)] = (n : ℝ) * ((n : ℝ) - 1) * (p : ℝ) ^ 2 := by
  have h := hX.integral_comp (f := fun x : ℝ => x * (x - 1)) (by fun_prop)
  rw [← integral_mul_sub_one_map_cast_binomial, ← h]
  rfl

/-- **Second moment of a binomial random variable**: if `X` has law `Bin(ℝ, n, p)` then
`E[X²] = n p (1 - p) + (n p)²`. -/
theorem integral_sq_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) :
    P[X ^ 2] = (n : ℝ) * p * (1 - (p : ℝ)) + ((n : ℝ) * p) ^ 2 := by
  have h := hX.integral_comp (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [← integral_sq_map_cast_binomial, ← h]
  rfl

/-- **Variance of a binomial random variable**: if `X` has law `Bin(ℝ, n, p)` then
`Var X = n p (1 - p)`. -/
theorem variance_of_hasLaw_binomial (hX : HasLaw X Bin(ℝ, n, p) P) :
    Var[X; P] = (n : ℝ) * p * (1 - (p : ℝ)) := by
  rw [hX.variance_eq, variance_id_map_cast_binomial]

end ProbabilityTheory
