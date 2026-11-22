/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Basic.Real.Basic

/-!
# L1 norm of a polynomial

This file defines the sum of the absolute values of a polynomial's coefficients.
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Semiring K]

/-- The L1 norm of a polynomial with respect to an absolute value. -/
noncomputable def l1Norm (v : AbsoluteValue K ℝ) (p : Polynomial K) : ℝ :=
  p.sum fun _ a ↦ v a

/-- The L1 norm as a sum over the polynomial's support. -/
theorem l1Norm_def (v : AbsoluteValue K ℝ) (p : Polynomial K) :
    l1Norm v p = ∑ i ∈ p.support, v (p.coeff i) :=
  rfl

/-- The L1 norm of the zero polynomial is zero. -/
@[simp]
theorem l1Norm_zero (v : AbsoluteValue K ℝ) :
    l1Norm v (0 : Polynomial K) = 0 := by
  simp [l1Norm]

/-- The L1 norm of a polynomial is nonnegative. -/
theorem l1Norm_nonneg (v : AbsoluteValue K ℝ) (p : Polynomial K) :
    0 ≤ l1Norm v p := by
  rw [l1Norm_def]
  exact Finset.sum_nonneg fun i _ ↦ v.nonneg _

/-- The L1 norm as a sum over all degrees through the natural degree. -/
theorem l1Norm_eq_sum_range (v : AbsoluteValue K ℝ) (p : Polynomial K) :
    l1Norm v p = ∑ i ∈ Finset.range (p.natDegree + 1), v (p.coeff i) := by
  rw [l1Norm_def]
  apply Finset.sum_subset supp_subset_range_natDegree_succ
  intro i _ hi
  rw [Polynomial.mem_support_iff, not_not] at hi
  rw [hi, map_zero]

/-- For a monic polynomial, the leading coefficient contributes one to the L1 norm. -/
theorem l1Norm_eq_sum_range_add_one_of_monic [Nontrivial K]
    (v : AbsoluteValue K ℝ) (f : Polynomial K) (hf : f.Monic) :
    l1Norm v f = (∑ i ∈ Finset.range f.natDegree, v (f.coeff i)) + 1 := by
  rw [l1Norm_eq_sum_range, Finset.sum_range_succ, coeff_natDegree,
    hf.leadingCoeff, map_one v]

/-- The L1 norm of a monic polynomial is at least one. -/
theorem one_le_l1Norm_of_monic [Nontrivial K]
    (v : AbsoluteValue K ℝ) (f : Polynomial K) (hf : f.Monic) :
    1 ≤ l1Norm v f := by
  have h1 : v (f.coeff f.natDegree) = 1 := by
    rw [coeff_natDegree, hf.leadingCoeff, map_one v]
  rw [l1Norm_eq_sum_range, ← h1]
  exact Finset.single_le_sum (fun i _ ↦ v.nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_self _))

end Polynomial
