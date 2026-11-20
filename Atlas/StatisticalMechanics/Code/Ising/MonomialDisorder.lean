/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.GKS

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech.Ising

noncomputable section

variable {V P : Type*} [Fintype V] [DecidableEq V]
  [Fintype P] [DecidableEq P]



def monomialInteractionPartition
    (K : P -> Real) (fac : P -> ConfigSpace V -> Real) : Real :=
  ∑ sigma : ConfigSpace V, Real.exp (∑ p : P, K p * fac p sigma)


def reverseInteractionCoupling (K : P -> Real) (D : Finset P) : P -> Real :=
  fun p => if p ∈ D then -K p else K p

theorem sum_reverseInteractionCoupling
    (K : P -> Real) (D : Finset P) (f : P -> Real) :
    (∑ p : P, reverseInteractionCoupling K D p * f p) =
      (∑ p : P, K p * f p) - 2 * ∑ p ∈ D, K p * f p := by
  calc
    (∑ p : P, reverseInteractionCoupling K D p * f p) =
        ∑ p : P, (K p * f p - if p ∈ D then 2 * K p * f p else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∈ D
      · simp [reverseInteractionCoupling, hp]
        ring
      · simp [reverseInteractionCoupling, hp]
    _ = (∑ p : P, K p * f p) -
        ∑ p : P, if p ∈ D then 2 * K p * f p else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ p : P, K p * f p) -
        ∑ p ∈ D, 2 * K p * f p := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_of_subset (Finset.subset_univ D)]
    _ = (∑ p : P, K p * f p) - 2 * ∑ p ∈ D, K p * f p := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring


theorem isSpinMonomial_finsetProd
    (fac : P -> ConfigSpace V -> Real)
    (hfac : forall p, IsSpinMonomial (fac p)) (S : Finset P) :
    IsSpinMonomial (fun sigma => ∏ p ∈ S, fac p sigma) := by
  induction S using Finset.induction with
  | empty => simpa using (IsSpinMonomial.const_one (V := V))
  | @insert p S hp ih =>
      simp_rw [Finset.prod_insert hp]
      exact (hfac p).mul ih



theorem monomialInteractionPartition_eq_powerset
    (K : P -> Real) (fac : P -> ConfigSpace V -> Real)
    (hpm : forall p sigma, fac p sigma = 1 ∨ fac p sigma = -1) :
    monomialInteractionPartition K fac =
      ∑ S ∈ (Finset.univ : Finset P).powerset,
        (∏ p ∈ S, Real.cosh (K p)) *
          (∏ p ∈ (Finset.univ : Finset P) \ S, Real.sinh (K p)) *
          ∑ sigma : ConfigSpace V,
            ∏ p ∈ (Finset.univ : Finset P) \ S, fac p sigma := by
  unfold monomialInteractionPartition
  calc
    (∑ sigma : ConfigSpace V, Real.exp (∑ p : P, K p * fac p sigma)) =
        ∑ sigma : ConfigSpace V,
          ∏ p : P, (Real.cosh (K p) + fac p sigma * Real.sinh (K p)) := by
      apply Finset.sum_congr rfl
      intro sigma _
      rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro p _
      exact exp_mul_pm (K p) (fac p sigma) (hpm p sigma)
    _ = ∑ sigma : ConfigSpace V,
        ∑ S ∈ (Finset.univ : Finset P).powerset,
          (∏ p ∈ S, Real.cosh (K p)) *
            ∏ p ∈ (Finset.univ : Finset P) \ S,
              (fac p sigma * Real.sinh (K p)) := by
      apply Finset.sum_congr rfl
      intro sigma _
      rw [Finset.prod_add]
    _ = ∑ S ∈ (Finset.univ : Finset P).powerset,
        ∑ sigma : ConfigSpace V,
          (∏ p ∈ S, Real.cosh (K p)) *
            ∏ p ∈ (Finset.univ : Finset P) \ S,
              (fac p sigma * Real.sinh (K p)) := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      calc
        (∑ sigma : ConfigSpace V,
            (∏ p ∈ S, Real.cosh (K p)) *
            ∏ p ∈ (Finset.univ : Finset P) \ S,
              (fac p sigma * Real.sinh (K p))) =
            (∏ p ∈ S, Real.cosh (K p)) *
              ∑ sigma : ConfigSpace V,
                ∏ p ∈ (Finset.univ : Finset P) \ S,
                  (fac p sigma * Real.sinh (K p)) := by
          rw [Finset.mul_sum]
        _ = (∏ p ∈ S, Real.cosh (K p)) *
            ∑ sigma : ConfigSpace V,
              ((∏ p ∈ (Finset.univ : Finset P) \ S, Real.sinh (K p)) *
                ∏ p ∈ (Finset.univ : Finset P) \ S, fac p sigma) := by
          congr 1
          apply Finset.sum_congr rfl
          intro sigma _
          rw [Finset.prod_mul_distrib]
          ring
        _ = (∏ p ∈ S, Real.cosh (K p)) *
            (∏ p ∈ (Finset.univ : Finset P) \ S, Real.sinh (K p)) *
              ∑ sigma : ConfigSpace V,
                ∏ p ∈ (Finset.univ : Finset P) \ S, fac p sigma := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro sigma _
          ring



theorem monomialInteractionPartition_reverse_le
    (K : P -> Real) (fac : P -> ConfigSpace V -> Real)
    (hK : forall p, 0 <= K p)
    (hfac : forall p, IsSpinMonomial (fac p))
    (hpm : forall p sigma, fac p sigma = 1 ∨ fac p sigma = -1)
    (D : Finset P) :
    monomialInteractionPartition (reverseInteractionCoupling K D) fac <=
      monomialInteractionPartition K fac := by
  rw [monomialInteractionPartition_eq_powerset _ fac hpm,
    monomialInteractionPartition_eq_powerset K fac hpm]
  apply Finset.sum_le_sum
  intro S hS
  have hmono : 0 <= ∑ sigma : ConfigSpace V,
      ∏ p ∈ (Finset.univ : Finset P) \ S, fac p sigma :=
    (isSpinMonomial_finsetProd fac hfac _).sum_nonneg
  have hcosh : (∏ p ∈ S,
      Real.cosh (reverseInteractionCoupling K D p)) =
      ∏ p ∈ S, Real.cosh (K p) := by
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hpD : p ∈ D
    · simp [reverseInteractionCoupling, hpD, Real.cosh_neg]
    · simp [reverseInteractionCoupling, hpD]
  rw [hcosh]
  have hcosh_nonneg : 0 <= ∏ p ∈ S, Real.cosh (K p) :=
    Finset.prod_nonneg (fun p _ => (Real.cosh_pos (K p)).le)
  have hsinh_nonneg : 0 <= ∏ p ∈ (Finset.univ : Finset P) \ S,
      Real.sinh (K p) :=
    Finset.prod_nonneg (fun p _ => Real.sinh_nonneg_iff.mpr (hK p))
  have hsinh_abs :
      |∏ p ∈ (Finset.univ : Finset P) \ S,
          Real.sinh (reverseInteractionCoupling K D p)| =
        ∏ p ∈ (Finset.univ : Finset P) \ S, Real.sinh (K p) := by
    rw [abs_prod]
    apply Finset.prod_congr rfl
    intro p hp
    by_cases hpD : p ∈ D
    · simp [reverseInteractionCoupling, hpD, Real.sinh_neg,
        abs_of_nonneg (Real.sinh_nonneg_iff.mpr (hK p))]
    · simp [reverseInteractionCoupling, hpD,
        abs_of_nonneg (Real.sinh_nonneg_iff.mpr (hK p))]
  have hsinh_le :
      (∏ p ∈ (Finset.univ : Finset P) \ S,
          Real.sinh (reverseInteractionCoupling K D p)) <=
        ∏ p ∈ (Finset.univ : Finset P) \ S, Real.sinh (K p) :=
    (le_abs_self _).trans_eq hsinh_abs
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hsinh_le hmono) hcosh_nonneg

end

end StatMech.Ising
