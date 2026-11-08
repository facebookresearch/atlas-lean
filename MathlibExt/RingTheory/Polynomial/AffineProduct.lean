/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Adapted from `eth/proof/networks/Eight/SecCrossing_PiecesAC.lean` in
https://github.com/anthropics/formal-math at commit
16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
generalize the polynomial identities to arbitrary finite index types and
commutative semirings, and isolate the integer coefficient bound.
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Products of affine linear polynomials

This module expands a finite product of factors `C (r s) + X * C (c s)` and
extracts its coefficients. It also bounds integer coefficients when every
constant and linear coefficient has absolute value at most one.
-/

@[expose] public section

open Polynomial

namespace Finset

/-- Expand a product of affine linear polynomials by the subset of factors
from which the linear term is selected. -/
theorem prod_C_add_X_mul_C_eq_sum {ι R : Type*} [DecidableEq ι]
    [CommSemiring R]
    (S : Finset ι) (r c : ι → R) :
    ∏ s ∈ S, (C (r s) + X * C (c s)) =
      ∑ Q ∈ S.powerset,
        C (∏ s ∈ S, if s ∈ Q then c s else r s) * X ^ #Q := by
  classical
  simp_rw [add_comm (C (r _))]
  rw [Finset.prod_add]
  refine sum_congr rfl fun Q hQ => ?_
  have hQ' := mem_powerset.1 hQ
  rw [prod_ite, filter_mem_eq_inter, filter_notMem_eq_sdiff,
    inter_eq_right.2 hQ', prod_mul_distrib, prod_const, C_mul, map_prod,
    map_prod]
  ring

/-- The coefficient of degree `i` in a product of affine linear polynomials is
the sum over the `i` factors from which the linear term is selected. -/
theorem prod_C_add_X_mul_C_coeff {ι R : Type*} [DecidableEq ι]
    [CommSemiring R] (S : Finset ι) (r c : ι → R) (i : ℕ) :
    (∏ s ∈ S, (C (r s) + X * C (c s))).coeff i =
      ∑ Q ∈ S.powersetCard i,
        ∏ s ∈ S, if s ∈ Q then c s else r s := by
  rw [prod_C_add_X_mul_C_eq_sum, finsetSum_coeff,
    powersetCard_eq_filter, sum_filter]
  refine sum_congr rfl fun Q _ => ?_
  rw [coeff_C_mul_X_pow]
  simp only [eq_comm]

/-- A product of affine linear polynomials has degree at most the number of
factors. -/
theorem prod_C_add_X_mul_C_natDegree_le {ι R : Type*} [CommSemiring R]
    (S : Finset ι) (r c : ι → R) :
    (∏ s ∈ S, (C (r s) + X * C (c s))).natDegree ≤ #S := by
  refine (natDegree_prod_le S _).trans ?_
  have h : ∀ s ∈ S, (C (r s) + X * C (c s)).natDegree ≤ 1 := by
    intro s _
    simpa only [X_mul_C, add_comm] using
      (natDegree_linear_le (a := c s) (b := r s))
  simpa using sum_le_card_nsmul S _ 1 h

/-- If every constant and linear coefficient is at most one in absolute value,
then the absolute value of coefficient `i` is at most `S.card.choose i`. -/
theorem abs_prod_C_add_X_mul_C_coeff_le_choose {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (r c : ι → ℤ) (i : ℕ)
    (hr : ∀ s ∈ S, |r s| ≤ 1) (hc : ∀ s ∈ S, |c s| ≤ 1) :
    |(∏ s ∈ S, (C (r s) + X * C (c s))).coeff i| ≤
      ((#S).choose i : ℤ) := by
  rw [prod_C_add_X_mul_C_coeff]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ Q ∈ S.powersetCard i,
      |∏ s ∈ S, if s ∈ Q then c s else r s| ≤ 1 := by
    intro Q _
    rw [Finset.abs_prod]
    calc
      (∏ s ∈ S, |if s ∈ Q then c s else r s|) ≤
          ∏ _s ∈ S, (1 : ℤ) := by
        refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun s hs => ?_
        split_ifs
        · exact hc s hs
        · exact hr s hs
      _ = 1 := by simp
  simpa using sum_le_card_nsmul _ _ 1 h

end Finset
