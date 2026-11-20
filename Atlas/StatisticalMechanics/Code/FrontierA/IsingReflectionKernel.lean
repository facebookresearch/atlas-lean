/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset Filter
open scoped BigOperators

namespace StatMech.FrontierA

variable {I C : Type*} [Fintype I] [Fintype C]



theorem dotProduct_pow_kernel_quadratic_eq_squares
    (u : I → C → Real) (a : I → Real) (n : Nat) :
    (∑ i : I, ∑ j : I, a i * a j * (∑ c : C, u i c * u j c) ^ n) =
      ∑ p : Fin n → C, (∑ i : I, a i * ∏ r : Fin n, u i (p r)) ^ 2 := by
  calc
    (∑ i : I, ∑ j : I, a i * a j * (∑ c : C, u i c * u j c) ^ n) =
        ∑ i : I, ∑ j : I,
        a i * a j * ∑ p : Fin n → C,
          ∏ r : Fin n, u i (p r) * u j (p r) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_pow]
    _ =
        ∑ i : I, ∑ j : I, ∑ p : Fin n → C,
          a i * a j * ∏ r : Fin n, u i (p r) * u j (p r) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ p : Fin n → C, ∑ j : I,
          a i * a j * ∏ r : Fin n, u i (p r) * u j (p r) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ p : Fin n → C, ∑ i : I, ∑ j : I,
          a i * a j * ∏ r : Fin n, u i (p r) * u j (p r) := by
      rw [Finset.sum_comm]
    _ = ∑ p : Fin n → C,
        (∑ i : I, a i * ∏ r : Fin n, u i (p r)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.prod_mul_distrib]
      ring



theorem dotProduct_pow_kernel_quadratic_nonneg
    (u : I → C → Real) (a : I → Real) (n : Nat) :
    0 ≤ ∑ i : I, ∑ j : I,
      a i * a j * (∑ c : C, u i c * u j c) ^ n := by
  rw [dotProduct_pow_kernel_quadratic_eq_squares]
  exact Finset.sum_nonneg fun p _ => sq_nonneg _



theorem exp_dotProduct_kernel_quadratic_nonneg
    (beta : Real) (hbeta : 0 ≤ beta)
    (u : I → C → Real) (a : I → Real) :
    0 ≤ ∑ i : I, ∑ j : I,
      a i * a j * Real.exp (beta * ∑ c : C, u i c * u j c) := by
  let q : Nat → Real := fun n =>
    ∑ i : I, ∑ j : I,
      a i * a j * ((beta * ∑ c : C, u i c * u j c) ^ n / n.factorial)
  have hq_nonneg : ∀ n, 0 ≤ q n := by
    intro n
    have hbetaPow : 0 ≤ beta ^ n := pow_nonneg hbeta n
    have hfac : 0 ≤ (n.factorial : Real) := by positivity
    have heq : q n = (beta ^ n / n.factorial) *
        (∑ i : I, ∑ j : I,
          a i * a j * (∑ c : C, u i c * u j c) ^ n) := by
      dsimp only [q]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_pow]
      ring
    rw [heq]
    exact mul_nonneg (div_nonneg hbetaPow hfac)
      (dotProduct_pow_kernel_quadratic_nonneg u a n)
  have hseries : HasSum q
      (∑ i : I, ∑ j : I,
        a i * a j * Real.exp (beta * ∑ c : C, u i c * u j c)) := by
    dsimp only [q]
    apply hasSum_sum
    intro i _
    apply hasSum_sum
    intro j _
    have hexp := NormedSpace.expSeries_div_hasSum_exp
      (beta * ∑ c : C, u i c * u j c)
    rw [← Real.exp_eq_exp_ℝ] at hexp
    simpa only [mul_div_assoc] using
      (hexp.mul_left (a i * a j))
  rw [← hseries.tsum_eq]
  exact tsum_nonneg hq_nonneg




theorem exp_dotProduct_kernel_reflection_inequality
    (beta : Real) (hbeta : 0 ≤ beta)
    (u : I → C → Real) (A B : I → Real) :
    2 * (∑ i : I, ∑ j : I,
      A i * B j * Real.exp (beta * ∑ c : C, u i c * u j c)) ≤
      (∑ i : I, ∑ j : I,
        A i * A j * Real.exp (beta * ∑ c : C, u i c * u j c)) +
      ∑ i : I, ∑ j : I,
        B i * B j * Real.exp (beta * ∑ c : C, u i c * u j c) := by
  have h := exp_dotProduct_kernel_quadratic_nonneg beta hbeta u
    (fun i => A i - B i)
  have hsymm : (∑ i : I, ∑ j : I,
      B i * A j * Real.exp (beta * ∑ c : C, u i c * u j c)) =
      ∑ i : I, ∑ j : I,
        A i * B j * Real.exp (beta * ∑ c : C, u i c * u j c) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hdot : (∑ c : C, u j c * u i c) =
        ∑ c : C, u i c * u j c := by
      apply Finset.sum_congr rfl
      intro c _
      ring
    rw [hdot]
    ring
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib] at h
  simp_rw [sub_mul, Finset.sum_sub_distrib] at h
  rw [hsymm] at h
  linarith

set_option maxRecDepth 10000 in



theorem exp_dotProduct_two_family_reflection_inequality
    (beta : Real) (hbeta : 0 ≤ beta)
    (u v : I → C → Real) (A B : I → Real) :
    2 * (∑ i : I, ∑ j : I,
      A i * B j * Real.exp (beta * ∑ c : C, u i c * v j c)) ≤
      (∑ i : I, ∑ j : I,
        A i * A j * Real.exp (beta * ∑ c : C, u i c * u j c)) +
      ∑ i : I, ∑ j : I,
        B i * B j * Real.exp (beta * ∑ c : C, v i c * v j c) := by
  let w : (Bool × I) → C → Real := fun p =>
    if p.1 then v p.2 else u p.2
  let A' : Bool × I → Real := fun p => if p.1 then 0 else A p.2
  let B' : Bool × I → Real := fun p => if p.1 then B p.2 else 0
  have h := exp_dotProduct_kernel_reflection_inequality
    (I := Bool × I) beta hbeta w A' B'
  dsimp only [w, A', B'] at h
  simp only [Fintype.sum_prod_type] at h
  simp only [Fintype.sum_bool, Bool.false_eq_true, if_false, if_true,
    zero_mul, mul_zero,
    Finset.sum_const_zero, zero_add, add_zero] at h
  exact h

end StatMech.FrontierA
