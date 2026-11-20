/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
open Real Finset

set_option linter.style.longLine false

namespace StatMech
namespace OSSS.RussoPrefactor








theorem rp_denom_pos {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    0 < Real.exp (β * J) - 1 := by
  have h1 : (1 : ℝ) < Real.exp (β * J) := Real.one_lt_exp_iff.mpr (by positivity)
  linarith




theorem rp_prefactor_pos {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    0 < J / (Real.exp (β * J) - 1) :=
  div_pos hJ (rp_denom_pos hJ hβ)













theorem rp_prefactor_antitone_beta {J β β₀ : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hββ : β ≤ β₀) :
    J / (Real.exp (β₀ * J) - 1) ≤ J / (Real.exp (β * J) - 1) := by
  have hden_pos : 0 < Real.exp (β * J) - 1 := rp_denom_pos hJ hβ
  have hmono : Real.exp (β * J) ≤ Real.exp (β₀ * J) := by
    apply Real.exp_le_exp.mpr; nlinarith
  apply div_le_div_of_nonneg_left hJ.le hden_pos
  linarith














theorem rp_minPrefactor {E : Type*} [Fintype E] [Nonempty E] (g : E → ℝ)
    (hg : ∀ e, 0 < g e) :
    ∃ cR : ℝ, 0 < cR ∧ ∀ e, cR ≤ g e := by
  obtain ⟨e₀, _, he₀⟩ :=
    Finset.exists_min_image Finset.univ g ⟨Classical.arbitrary E, Finset.mem_univ _⟩
  exact ⟨g e₀, hg e₀, fun e => he₀ e (Finset.mem_univ _)⟩






















theorem rp_prefactor_extraction {E : Type*} [Fintype E] (g Cov : E → ℝ) (cR : ℝ)
    (hg : ∀ e, cR ≤ g e) (hCov : ∀ e, 0 ≤ Cov e) :
    cR * ∑ e, Cov e ≤ ∑ e, g e * Cov e := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  exact mul_le_mul_of_nonneg_right (hg e) (hCov e)





























theorem rp_differential_lower {E : Type*} [Fintype E] [Nonempty E]
    (g Cov : E → ℝ) (θ' : ℝ)
    (hg : ∀ e, 0 < g e) (hCov : ∀ e, 0 ≤ Cov e)
    (hderiv : θ' = ∑ e, g e * Cov e) :
    ∃ cR : ℝ, 0 < cR ∧ cR * ∑ e, Cov e ≤ θ' := by
  obtain ⟨cR, hcRpos, hcRle⟩ := rp_minPrefactor g hg
  refine ⟨cR, hcRpos, ?_⟩
  rw [hderiv]
  exact rp_prefactor_extraction g Cov cR hcRle hCov














theorem rp_differential_lower_weighted {E : Type*} [Fintype E] [Nonempty E]
    (J Cov : E → ℝ) (β θ' : ℝ) (hJ : ∀ e, 0 < J e) (hβ : 0 < β)
    (hCov : ∀ e, 0 ≤ Cov e)
    (hderiv : θ' = ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e) :
    ∃ cR : ℝ, 0 < cR ∧ cR * ∑ e, Cov e ≤ θ' :=
  rp_differential_lower (fun e => J e / (Real.exp (β * J e) - 1)) Cov θ'
    (fun e => rp_prefactor_pos (hJ e) hβ) hCov hderiv



theorem rp_differential_lower_weighted_beta {E : Type*} [Fintype E] [Nonempty E]
    (J Cov : E → ℝ) (β θ' : ℝ) (hJ : ∀ e, 0 < J e) (hβ : 0 < β)
    (hCov : ∀ e, 0 ≤ Cov e)
    (hderiv : θ' = ∑ e, (J e / (1 - Real.exp (-(β * J e)))) * Cov e) :
    ∃ cR : ℝ, 0 < cR ∧ cR * ∑ e, Cov e ≤ θ' := by
  apply rp_differential_lower
      (fun e => J e / (1 - Real.exp (-(β * J e)))) Cov θ'
      _ hCov hderiv
  intro e
  apply div_pos (hJ e)
  have hβJ : 0 < β * J e := mul_pos hβ (hJ e)
  have hexp : Real.exp (-(β * J e)) < 1 :=
    Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβJ)
  linarith


theorem rp_beta_prefactor_antitone {J β β₀ : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hββ₀ : β ≤ β₀) :
    J / (1 - Real.exp (-(β₀ * J))) ≤
      J / (1 - Real.exp (-(β * J))) := by
  have hden : 0 < 1 - Real.exp (-(β * J)) := by
    have hβJ : 0 < β * J := mul_pos hβ hJ
    have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβJ)
    linarith
  have hexp : Real.exp (-(β₀ * J)) ≤ Real.exp (-(β * J)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  apply div_le_div_of_nonneg_left hJ.le hden
  linarith


theorem rp_differential_lower_weighted_beta_uniform
    {E : Type*} [Fintype E] [Nonempty E]
    (J Cov : E → ℝ) (β β₀ θ' : ℝ) (hJ : ∀ e, 0 < J e)
    (hβ : 0 < β) (hββ₀ : β ≤ β₀) (hCov : ∀ e, 0 ≤ Cov e)
    (hderiv : θ' = ∑ e, (J e / (1 - Real.exp (-(β * J e)))) * Cov e) :
    ∃ cR : ℝ, 0 < cR ∧
      (∀ e, cR ≤ J e / (1 - Real.exp (-(β₀ * J e)))) ∧
      cR * ∑ e, Cov e ≤ θ' := by
  have hβ₀ : 0 < β₀ := lt_of_lt_of_le hβ hββ₀
  obtain ⟨cR, hcR, hcRle⟩ := rp_minPrefactor
    (fun e => J e / (1 - Real.exp (-(β₀ * J e)))) (fun e => by
      apply div_pos (hJ e)
      have hβJ : 0 < β₀ * J e := mul_pos hβ₀ (hJ e)
      have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hβJ)
      linarith)
  refine ⟨cR, hcR, hcRle, ?_⟩
  rw [hderiv]
  apply rp_prefactor_extraction
  · intro e
    exact (hcRle e).trans (rp_beta_prefactor_antitone (hJ e) hβ hββ₀)
  · exact hCov

end OSSS.RussoPrefactor
end StatMech
