/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Russo-type prefactors for weighted random-cluster derivatives

For edge weights `p_e = 1 - e^{-β J_e}` the derivative of a random-cluster probability in `β` is a
sum over edges of a positive prefactor times a nonnegative covariance. On a finite edge set the
prefactors are bounded below by a positive constant `c_R`, so the derivative is at least
`c_R ∑_e Cov_e`. This file proves these elementary bounds for the two prefactor forms
`J / (e^{βJ} - 1)` and `J / (1 - e^{-βJ})`; the derivative formula itself is a hypothesis
(`hderiv`).

## Main results

* `StatMech.OSSS.RussoPrefactor.rp_differential_lower`: `θ' = ∑ g_e Cov_e` with `g > 0`,
  `Cov ≥ 0` gives `θ' ≥ c_R ∑ Cov_e` for some `c_R > 0`.
* `StatMech.OSSS.RussoPrefactor.rp_differential_lower_weighted`,
  `rp_differential_lower_weighted_beta`: the two prefactor forms.
* `StatMech.OSSS.RussoPrefactor.rp_differential_lower_weighted_beta_uniform`: a constant uniform
  for `β' ∈ [β, β₀]`.

## Implementation notes

For `p_e = 1 - e^{-βJ_e}` the Russo formula `dφ(A)/dp_e = Cov(ω_e, 1_A) / (p_e (1 - p_e))` gives the
prefactor `(dp_e/dβ) / (p_e (1 - p_e)) = J_e / (1 - e^{-βJ_e})`, as in the `_beta` variants. The
prefactor `J_e / (e^{βJ_e} - 1)` equals `e^{-βJ_e}` times this. So `hderiv` in its form
`θ' = ∑ (J_e / (e^{βJ_e} - 1)) Cov_e` matches the derivative only if `Cov_e` is normalized
differently (for example as `Cov(ω_e, 1_A) / (1 - p_e)`). This file does not fix a normalization.

## References

* G. Grimmett, *The Random-Cluster Model*, Springer, 2006, Chapter 2.
-/

@[expose] public section

open scoped BigOperators
open Real Finset

namespace StatMech
namespace OSSS.RussoPrefactor

/-- `e^{βJ} - 1 > 0` for `J, β > 0`. -/
theorem rp_denom_pos {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    0 < Real.exp (β * J) - 1 := by
  have h1 : (1 : ℝ) < Real.exp (β * J) := Real.one_lt_exp_iff.mpr (by positivity)
  linarith

/-- `J / (e^{βJ} - 1) > 0` for `J, β > 0`. -/
theorem rp_prefactor_pos {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    0 < J / (Real.exp (β * J) - 1) :=
  div_pos hJ (rp_denom_pos hJ hβ)

/-- `J / (e^{βJ} - 1)` is antitone in `β > 0`. -/
theorem rp_prefactor_antitone_beta {J β β₀ : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hββ : β ≤ β₀) :
    J / (Real.exp (β₀ * J) - 1) ≤ J / (Real.exp (β * J) - 1) := by
  have hden_pos : 0 < Real.exp (β * J) - 1 := rp_denom_pos hJ hβ
  have hmono : Real.exp (β * J) ≤ Real.exp (β₀ * J) := by
    apply Real.exp_le_exp.mpr; nlinarith
  apply div_le_div_of_nonneg_left hJ.le hden_pos
  linarith

/-- A positive function on a finite nonempty type has a positive lower bound (its minimum). -/
theorem rp_minPrefactor {E : Type*} [Finite E] [Nonempty E] (g : E → ℝ)
    (hg : ∀ e, 0 < g e) :
    ∃ cR : ℝ, 0 < cR ∧ ∀ e, cR ≤ g e := by
  obtain ⟨e₀, he₀⟩ := Finite.exists_min g
  exact ⟨g e₀, hg e₀, he₀⟩

/-- `c ≤ g_e` and `Cov_e ≥ 0` give `c ∑ Cov_e ≤ ∑ g_e Cov_e`. -/
theorem rp_prefactor_extraction {E : Type*} [Fintype E] (g Cov : E → ℝ) (cR : ℝ)
    (hg : ∀ e, cR ≤ g e) (hCov : ∀ e, 0 ≤ Cov e) :
    cR * ∑ e, Cov e ≤ ∑ e, g e * Cov e := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  exact mul_le_mul_of_nonneg_right (hg e) (hCov e)

/-- If `θ' = ∑ g_e Cov_e` with `g > 0` and `Cov ≥ 0` on a finite nonempty edge set, then `c_R ∑
Cov_e ≤ θ'` for some `c_R > 0`. -/
theorem rp_differential_lower {E : Type*} [Fintype E] [Nonempty E]
    (g Cov : E → ℝ) (θ' : ℝ)
    (hg : ∀ e, 0 < g e) (hCov : ∀ e, 0 ≤ Cov e)
    (hderiv : θ' = ∑ e, g e * Cov e) :
    ∃ cR : ℝ, 0 < cR ∧ cR * ∑ e, Cov e ≤ θ' := by
  obtain ⟨cR, hcRpos, hcRle⟩ := rp_minPrefactor g hg
  refine ⟨cR, hcRpos, ?_⟩
  rw [hderiv]
  exact rp_prefactor_extraction g Cov cR hcRle hCov

/-- `rp_differential_lower` for the prefactor `J_e / (e^{βJ_e} - 1)`; `hderiv` is assumed (see the
module docstring for its normalization). -/
theorem rp_differential_lower_weighted {E : Type*} [Fintype E] [Nonempty E]
    (J Cov : E → ℝ) (β θ' : ℝ) (hJ : ∀ e, 0 < J e) (hβ : 0 < β)
    (hCov : ∀ e, 0 ≤ Cov e)
    (hderiv : θ' = ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e) :
    ∃ cR : ℝ, 0 < cR ∧ cR * ∑ e, Cov e ≤ θ' :=
  rp_differential_lower (fun e => J e / (Real.exp (β * J e) - 1)) Cov θ'
    (fun e => rp_prefactor_pos (hJ e) hβ) hCov hderiv

/-- `rp_differential_lower` for the prefactor `J_e / (1 - e^{-βJ_e})`. -/
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

/-- `J / (1 - e^{-βJ})` is antitone in `β > 0`. -/
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

/-- `rp_differential_lower_weighted_beta` with a constant `c_R` that also bounds the prefactors at
`β₀ ≥ β`, hence works on `[β, β₀]`. -/
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
