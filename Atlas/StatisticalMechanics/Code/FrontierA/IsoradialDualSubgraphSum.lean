/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Ring.Commute
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Lean.Elab.Tactic.Omega













namespace StatMech.FrontierA

open Finset
open scoped BigOperators

variable {E K : Type*} [Fintype E] [DecidableEq E]


noncomputable def isoradialCriticalMu (theta : Real) : Complex :=
  Complex.I * (Real.tan theta : Complex)



theorem isoradialCriticalMu_dual (theta : Real) :
    isoradialCriticalMu (Real.pi / 2 - theta) =
      -(isoradialCriticalMu theta)⁻¹ := by
  rw [isoradialCriticalMu, isoradialCriticalMu,
    Real.tan_pi_div_two_sub]
  push_cast
  rw [mul_inv_rev, Complex.inv_I]
  simp only [mul_neg, neg_neg]
  ac_rfl


theorem isoradialCriticalMu_ne_zero {theta : Real}
    (htheta : 0 < theta) (htheta' : theta < Real.pi / 2) :
    isoradialCriticalMu theta ≠ 0 := by
  rw [isoradialCriticalMu, mul_ne_zero_iff]
  exact ⟨Complex.I_ne_zero,
    Complex.ofReal_ne_zero.mpr
      (Real.tan_pos_of_pos_of_lt_pi_div_two htheta htheta').ne'⟩


def finsetComplementEquiv : Finset E ≃ Finset E where
  toFun F := Fᶜ
  invFun F := Fᶜ
  left_inv F := compl_compl F
  right_inv F := compl_compl F

@[simp]
theorem finsetComplementEquiv_apply (F : Finset E) :
    finsetComplementEquiv F = Fᶜ := rfl



def kwDualSubgraphSum [CommSemiring K]
    (coefficient : Finset E -> K) (weight : E -> K) : K :=
  ∑ F : Finset E, coefficient F * ∏ e ∈ F, weight e

omit [Fintype E] [DecidableEq E] in



theorem prod_one_sub_inv
    [Field K] {B : Finset E} (character : E -> K)
    (hcharacter : forall e, e ∈ B -> character e ≠ 0) :
    (∏ e ∈ B, (1 - (character e)⁻¹)) =
      (-1 : K) ^ B.card * (∏ e ∈ B, character e)⁻¹ *
        ∏ e ∈ B, (1 - character e) := by
  have hpoint (e : E) (he : e ∈ B) :
      1 - (character e)⁻¹ =
        -(character e)⁻¹ * (1 - character e) := by
    rw [mul_sub, mul_one, neg_mul, inv_mul_cancel₀ (hcharacter e he)]
    simp only [sub_eq_add_neg, neg_neg]
    rw [add_comm]
  calc
    (∏ e ∈ B, (1 - (character e)⁻¹)) =
        ∏ e ∈ B, (-(character e)⁻¹) * (1 - character e) := by
      apply Finset.prod_congr rfl
      intro e he
      exact hpoint e he
    _ = (-1 : K) ^ B.card * (∏ e ∈ B, character e)⁻¹ *
        ∏ e ∈ B, (1 - character e) := by
      rw [prod_mul_distrib, prod_neg, prod_inv_distrib]

omit [Fintype E] [DecidableEq E] in


theorem prod_one_sub_inv_of_prod_eq_one
    [Field K] {B : Finset E} (character : E -> K)
    (hcharacter : forall e, e ∈ B -> character e ≠ 0)
    (htotal : ∏ e ∈ B, character e = 1) :
    (∏ e ∈ B, (1 - (character e)⁻¹)) =
      (-1 : K) ^ B.card * ∏ e ∈ B, (1 - character e) := by
  rw [prod_one_sub_inv character hcharacter, htotal, inv_one, mul_one]





theorem compl_card_add_boundary_mod_two_constant
    (boundaryComponents : Finset E -> Nat)
    (htoggle : forall (F : Finset E) (e : E), e ∉ F ->
      boundaryComponents (insert e F) % 2 =
        (boundaryComponents F + 1) % 2) :
    forall F : Finset E,
      (Fᶜ.card + boundaryComponents F) % 2 =
        (Fintype.card E + boundaryComponents ∅) % 2 := by
  intro F
  induction F using Finset.induction_on with
  | empty => simp
  | @insert e F he ih =>
      have hcompl : Fᶜ.card = (insert e F)ᶜ.card + 1 := by
        have hsets : Fᶜ = insert e (insert e F)ᶜ := by
          ext x
          by_cases hx : x = e
          · subst x
            simp [he]
          · simp [hx]
        rw [hsets, card_insert_of_notMem]
        simp
      have hb := htoggle F e he
      omega



theorem compl_card_add_boundary_mod_two_eq_dualVertexCount
    (boundaryComponents : Finset E -> Nat) (dualVertexCount : Nat)
    (htoggle : forall (F : Finset E) (e : E), e ∉ F ->
      boundaryComponents (insert e F) % 2 =
        (boundaryComponents F + 1) % 2)
    (hbase : (Fintype.card E + boundaryComponents ∅) % 2 =
      dualVertexCount % 2) :
    forall F : Finset E,
      (Fᶜ.card + boundaryComponents F) % 2 = dualVertexCount % 2 := by
  intro F
  rw [compl_card_add_boundary_mod_two_constant boundaryComponents htoggle F,
    hbase]



theorem inv_univ_prod_mul_prod_eq_compl_prod
    [Field K] (weight : E -> K) (hweight : forall e, weight e ≠ 0)
    (F : Finset E) :
    (∏ e : E, weight e)⁻¹ * (∏ e ∈ F, weight e) =
      ∏ e ∈ Fᶜ, (weight e)⁻¹ := by
  have hF : ∏ e ∈ F, weight e ≠ 0 :=
    prod_ne_zero_iff.mpr fun e _ => hweight e
  have hsplit := prod_sdiff (f := fun e => (weight e)⁻¹)
    (show F ⊆ (univ : Finset E) by simp)
  have hsplit' :
      (∏ e ∈ Fᶜ, (weight e)⁻¹) * (∏ e ∈ F, (weight e)⁻¹) =
        (∏ e : E, weight e)⁻¹ := by
    simpa only [compl_eq_univ_sdiff, prod_inv_distrib] using hsplit
  have hFinv :
      (∏ e ∈ F, (weight e)⁻¹) = (∏ e ∈ F, weight e)⁻¹ :=
    prod_inv_distrib weight
  calc
    (∏ e : E, weight e)⁻¹ * (∏ e ∈ F, weight e) =
        ((∏ e ∈ Fᶜ, (weight e)⁻¹) *
          (∏ e ∈ F, (weight e)⁻¹)) * (∏ e ∈ F, weight e) := by rw [hsplit']
    _ = (∏ e ∈ Fᶜ, (weight e)⁻¹) *
          ((∏ e ∈ F, weight e)⁻¹ * (∏ e ∈ F, weight e)) := by
      rw [hFinv]
      ac_rfl
    _ = ∏ e ∈ Fᶜ, (weight e)⁻¹ := by rw [inv_mul_cancel₀ hF, mul_one]








theorem kwDualSubgraphSum_complement_duality
    [Field K]
    (coefficient dualCoefficient : Finset E -> K)
    (weight : E -> K) (hweight : forall e, weight e ≠ 0)
    (dualVertexCount : Nat)
    (hcoefficient : forall F : Finset E,
      (-1 : K) ^ Fᶜ.card * dualCoefficient Fᶜ =
        (-1 : K) ^ dualVertexCount * coefficient F) :
    kwDualSubgraphSum dualCoefficient (fun e => -(weight e)⁻¹) =
      (-1 : K) ^ dualVertexCount *
        ((∏ e : E, weight e)⁻¹ *
          kwDualSubgraphSum coefficient weight) := by
  rw [kwDualSubgraphSum, kwDualSubgraphSum]
  rw [← Equiv.sum_comp (finsetComplementEquiv (E := E))]
  simp only [finsetComplementEquiv_apply]
  rw [mul_sum, mul_sum]
  apply Finset.sum_congr rfl
  intro F _
  rw [prod_neg]
  have hc := hcoefficient F
  have hw := inv_univ_prod_mul_prod_eq_compl_prod weight hweight F
  calc
    dualCoefficient Fᶜ *
        ((-1 : K) ^ Fᶜ.card * ∏ e ∈ Fᶜ, (weight e)⁻¹) =
        ((-1 : K) ^ Fᶜ.card * dualCoefficient Fᶜ) *
          (∏ e ∈ Fᶜ, (weight e)⁻¹) := by ac_rfl
    _ = ((-1 : K) ^ dualVertexCount * coefficient F) *
          (∏ e ∈ Fᶜ, (weight e)⁻¹) := by rw [hc]
    _ = (-1 : K) ^ dualVertexCount *
        ((∏ e : E, weight e)⁻¹ *
          (coefficient F * ∏ e ∈ F, weight e)) := by
      rw [← hw]
      ac_rfl




theorem kwDualSubgraphSum_coefficient_sign_of_boundaryParity
    [Field K]
    (coefficient dualCoefficient : Finset E -> K)
    (boundaryComponents : Finset E -> Nat) (dualVertexCount : Nat)
    (hboundary : forall F : Finset E,
      dualCoefficient Fᶜ =
        (-1 : K) ^ boundaryComponents F * coefficient F)
    (hparity : forall F : Finset E,
      (Fᶜ.card + boundaryComponents F) % 2 = dualVertexCount % 2) :
    forall F : Finset E,
      (-1 : K) ^ Fᶜ.card * dualCoefficient Fᶜ =
        (-1 : K) ^ dualVertexCount * coefficient F := by
  intro F
  rw [hboundary F, ← mul_assoc, ← pow_add]
  have hsign : (-1 : K) ^ (Fᶜ.card + boundaryComponents F) =
      (-1 : K) ^ dualVertexCount := by
    calc
      (-1 : K) ^ (Fᶜ.card + boundaryComponents F) =
          (-1 : K) ^ ((Fᶜ.card + boundaryComponents F) % 2) :=
        neg_one_pow_eq_pow_mod_two _
      _ = (-1 : K) ^ (dualVertexCount % 2) := by rw [hparity F]
      _ = (-1 : K) ^ dualVertexCount :=
        (neg_one_pow_eq_pow_mod_two _).symm
  rw [hsign]



theorem kwDualSubgraphSum_complement_duality_of_boundaryParity
    [Field K]
    (coefficient dualCoefficient : Finset E -> K)
    (weight : E -> K) (hweight : forall e, weight e ≠ 0)
    (boundaryComponents : Finset E -> Nat) (dualVertexCount : Nat)
    (hboundary : forall F : Finset E,
      dualCoefficient Fᶜ =
        (-1 : K) ^ boundaryComponents F * coefficient F)
    (hparity : forall F : Finset E,
      (Fᶜ.card + boundaryComponents F) % 2 = dualVertexCount % 2) :
    kwDualSubgraphSum dualCoefficient (fun e => -(weight e)⁻¹) =
      (-1 : K) ^ dualVertexCount *
        ((∏ e : E, weight e)⁻¹ *
          kwDualSubgraphSum coefficient weight) :=
  kwDualSubgraphSum_complement_duality coefficient dualCoefficient weight hweight
    dualVertexCount
    (kwDualSubgraphSum_coefficient_sign_of_boundaryParity
      coefficient dualCoefficient boundaryComponents dualVertexCount
      hboundary hparity)

end StatMech.FrontierA
