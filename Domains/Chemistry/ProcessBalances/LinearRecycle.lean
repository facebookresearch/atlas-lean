/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.MMatrix

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Linear recycle networks

A finite nonreactive network has a linear steady balance. Its recycling matrix
sums all return fractions between each pair of units, allowing parallel edges
and self-loops. Summing the steady balances leaves just fresh and terminal flows.
-/

open scoped BigOperators Matrix

namespace Domains.Chemistry.ProcessBalances.LinearRecycle

/-- The edgewise steady balances are equivalent to the recycling matrix equation.
If the spectral radius of `K` is below one, the unique solution is `(1 - K)⁻¹ *ᵥ fresh`,
which is nonnegative. Total terminal flow equals total fresh feed for any solution,
without a spectral-radius assumption.

Source for the splitter balances: *Introduction to Chemical Engineering Processes*,
Wikibooks, [How to Analyze a Recycle System](https://en.wikibooks.org/wiki/Introduction_to_Chemical_Engineering_Processes/How_to_Analyze_a_Recycle_System). -/
public theorem linear_recycle_balances {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (send receive : E → V) (fraction : E → ℝ) (fresh : V → ℝ)
    (hfrac : ∀ e, 0 ≤ fraction e) (hfresh : ∀ i, 0 ≤ fresh i)
    (_hshares : ∀ j, (∑ e, if send e = j then fraction e else 0) ≤ 1) :
    let K : Matrix V V ℝ := fun i j =>
      ∑ e, if send e = j ∧ receive e = i then fraction e else 0
    let balanced (x : V → ℝ) := ∀ i, x i = fresh i +
      ∑ e, if receive e = i then fraction e * x (send e) else 0
    (∀ x, balanced x ↔ x = fresh + K *ᵥ x) ∧
    (spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) < 1 →
      IsUnit (1 - K) ∧ (∀ x, balanced x ↔ x = (1 - K)⁻¹ *ᵥ fresh) ∧
      (∀ i, 0 ≤ ((1 - K)⁻¹ *ᵥ fresh) i)) ∧
    (∀ x, balanced x →
      (∑ j, (1 - ∑ e, if send e = j then fraction e else 0) * x j) = ∑ i, fresh i) := by
  let K : Matrix V V ℝ := fun i j =>
    ∑ e, if send e = j ∧ receive e = i then fraction e else 0
  let balanced (x : V → ℝ) := ∀ i, x i = fresh i +
    ∑ e, if receive e = i then fraction e * x (send e) else 0
  have harrival (x : V → ℝ) (i : V) :
      (K *ᵥ x) i = ∑ e, if receive e = i then fraction e * x (send e) else 0 := by
    change (∑ j, (∑ e, if send e = j ∧ receive e = i then fraction e else 0) * x j) = _
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : receive e = i
    · simp only [he, and_true, ite_true, ite_mul, zero_mul]
      exact Fintype.sum_ite_eq (send e) (fun j => fraction e * x j)
    · simp [he]
  have hequiv (x : V → ℝ) : balanced x ↔ x = fresh + K *ᵥ x := by
    constructor
    · intro hx
      funext i
      simpa only [Pi.add_apply, harrival] using hx i
    · intro hx i
      simpa only [Pi.add_apply, harrival] using congrFun hx i
  refine ⟨hequiv, ?_, ?_⟩
  · intro hρ
    change spectralRadius ℂ (K.map (algebraMap ℝ ℂ)) < 1 at hρ
    have hu := Matrix.isUnit_one_sub_of_spectralRadius_lt_one hρ
    have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
    have hK (i j : V) : 0 ≤ K i j := by
      change 0 ≤ ∑ e, if send e = j ∧ receive e = i then fraction e else 0
      exact Finset.sum_nonneg fun e _ => by split <;> simp_all
    have hlinear (x : V → ℝ) : x = fresh + K *ᵥ x ↔ (1 - K) *ᵥ x = fresh := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_eq_iff_eq_add.symm
    refine ⟨hu, ?_, ?_⟩
    · intro x
      change balanced x ↔ x = (1 - K)⁻¹ *ᵥ fresh
      rw [hequiv, hlinear]
      constructor
      · intro hx
        calc
          x = (1 : Matrix V V ℝ) *ᵥ x := (Matrix.one_mulVec _).symm
          _ = ((1 - K)⁻¹ * (1 - K)) *ᵥ x := by rw [Matrix.nonsing_inv_mul _ hd]
          _ = (1 - K)⁻¹ *ᵥ fresh := by rw [← Matrix.mulVec_mulVec, hx]
      · intro hx
        rw [hx, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
    · intro i
      change 0 ≤ ∑ j, ((1 - K)⁻¹) i j * fresh j
      exact Finset.sum_nonneg fun j _ => mul_nonneg (Matrix.inv_one_sub_nonneg hK hρ i j) (hfresh j)
  · intro x hx
    have htotal : (∑ i, (K *ᵥ x) i) =
        ∑ j, (∑ e, if send e = j then fraction e else 0) * x j := by
      calc
        _ = ∑ i, ∑ e, if receive e = i then fraction e * x (send e) else 0 :=
          Finset.sum_congr rfl fun i _ => harrival x i
        _ = ∑ e, fraction e * x (send e) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun e _ =>
            Fintype.sum_ite_eq (receive e) (fun _ => fraction e * x (send e))
        _ = _ := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun e _ => ?_
          simp only [ite_mul, zero_mul]
          exact (Fintype.sum_ite_eq (send e) (fun j => fraction e * x j)).symm
    have hsum := congrArg (fun q : V → ℝ => ∑ i, q i) ((hequiv x).1 hx)
    simp only [Pi.add_apply, Finset.sum_add_distrib, htotal] at hsum
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
    linarith only [hsum]

end Domains.Chemistry.ProcessBalances.LinearRecycle
