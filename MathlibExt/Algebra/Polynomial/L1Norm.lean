/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Data.Real.Basic

/-!
# L1 norm of a polynomial

This file defines the sum of the absolute values of a polynomial's coefficients.
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Semiring K]

/-- **L1 norm of a polynomial.** Let $K$ be a semiring and $v$ a real-valued absolute value on
$K$. The L1 norm of a polynomial $p = \sum_i a_i X^i \in K[X]$ with respect to $v$ is the real
number $\|p\|_v = \sum_i v(a_i)$, where the sum runs over the indices $i$ with $a_i \neq 0$. -/
noncomputable def l1Norm (v : AbsoluteValue K ℝ) (p : Polynomial K) : ℝ :=
  p.sum fun _ a ↦ v a

/-- **L1 norm as a sum over the support.** Let $K$ be a semiring and $v$ a real-valued absolute
value on $K$. For every polynomial $p = \sum_i a_i X^i \in K[X]$, the L1 norm $\|p\|_v$ of $p$
with respect to $v$ equals $\sum_{i \in S} v(a_i)$, where $S = \{ i : a_i \neq 0 \}$ is the
support of $p$. -/
theorem l1Norm_def (v : AbsoluteValue K ℝ) (p : Polynomial K) :
    l1Norm v p = ∑ i ∈ p.support, v (p.coeff i) :=
  rfl

/-- **L1 norm of the zero polynomial.** Let $K$ be a semiring and $v$ a real-valued absolute value
on $K$. The L1 norm of the zero polynomial in $K[X]$ with respect to $v$ is $0$. -/
@[simp]
theorem l1Norm_zero (v : AbsoluteValue K ℝ) :
    l1Norm v (0 : Polynomial K) = 0 := by
  simp [l1Norm]

/-- **Nonnegativity of the L1 norm.** Let $K$ be a semiring and $v$ a real-valued absolute value
on $K$. For every polynomial $p \in K[X]$, the L1 norm of $p$ with respect to $v$ satisfies
$\|p\|_v \ge 0$. -/
theorem l1Norm_nonneg (v : AbsoluteValue K ℝ) (p : Polynomial K) :
    0 ≤ l1Norm v p := by
  rw [l1Norm_def]
  exact Finset.sum_nonneg fun i _ ↦ v.nonneg _

/-- **L1 norm as a sum up to the degree.** Let $K$ be a semiring and $v$ a real-valued absolute
value on $K$. Let $p = \sum_i a_i X^i \in K[X]$ and let $n$ be the degree of $p$, with $n = 0$
when $p = 0$. Then the L1 norm of $p$ with respect to $v$ is $\|p\|_v = \sum_{i=0}^{n} v(a_i)$. -/
theorem l1Norm_eq_sum_range (v : AbsoluteValue K ℝ) (p : Polynomial K) :
    l1Norm v p = ∑ i ∈ Finset.range (p.natDegree + 1), v (p.coeff i) := by
  rw [l1Norm_def]
  apply Finset.sum_subset supp_subset_range_natDegree_succ
  intro i _ hi
  rw [Polynomial.mem_support_iff, not_not] at hi
  rw [hi, map_zero]

/-- **L1 norm of a monic polynomial.** Let $K$ be a nontrivial semiring (one with $0 \neq 1$)
and $v$ a real-valued absolute value on $K$. If $f = \sum_i a_i X^i \in K[X]$ is monic of degree
$n$, then the L1 norm of $f$ with respect to $v$ is $\|f\|_v = \sum_{i=0}^{n-1} v(a_i) + 1$. -/
theorem l1Norm_eq_sum_range_add_one_of_monic [Nontrivial K]
    (v : AbsoluteValue K ℝ) (f : Polynomial K) (hf : f.Monic) :
    l1Norm v f = (∑ i ∈ Finset.range f.natDegree, v (f.coeff i)) + 1 := by
  rw [l1Norm_eq_sum_range, Finset.sum_range_succ, coeff_natDegree,
    hf.leadingCoeff, map_one v]

/-- **Monic polynomials have L1 norm at least one.** Let $K$ be a nontrivial semiring (one with
$0 \neq 1$) and $v$ a real-valued absolute value on $K$. If $f \in K[X]$ is monic, then the L1
norm of $f$ with respect to $v$ satisfies $\|f\|_v \ge 1$. -/
theorem one_le_l1Norm_of_monic [Nontrivial K]
    (v : AbsoluteValue K ℝ) (f : Polynomial K) (hf : f.Monic) :
    1 ≤ l1Norm v f := by
  have h1 : v (f.coeff f.natDegree) = 1 := by
    rw [coeff_natDegree, hf.leadingCoeff, map_one v]
  rw [l1Norm_eq_sum_range, ← h1]
  exact Finset.single_le_sum (fun i _ ↦ v.nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_self _))

end Polynomial
