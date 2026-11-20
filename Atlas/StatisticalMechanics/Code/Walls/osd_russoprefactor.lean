/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Code.OSSS.RussoPrefactor

open scoped BigOperators
open Real Finset

set_option linter.style.longLine false

namespace StatMech
namespace Walls

open StatMech.OSSS.RussoPrefactor











theorem wall_prefactor_pos {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    0 < J / (Real.exp (β * J) - 1) :=
  rp_prefactor_pos hJ hβ







theorem wall_prefactor_antitone_beta {J β β₀ : ℝ} (hJ : 0 < J) (hβ : 0 < β)
    (hββ : β ≤ β₀) :
    J / (Real.exp (β₀ * J) - 1) ≤ J / (Real.exp (β * J) - 1) :=
  rp_prefactor_antitone_beta hJ hβ hββ











theorem wall_minPrefactor_pos {E : Type*} [Fintype E] [Nonempty E] (g : E → ℝ)
    (hg : ∀ e, 0 < g e) :
    ∃ cR : ℝ, 0 < cR ∧ ∀ e, cR ≤ g e :=
  rp_minPrefactor g hg











theorem wall_oneSubExp_pos {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    0 < 1 - Real.exp (-(β * J)) := by
  have hbJ : 0 < β * J := by positivity
  have : Real.exp (-(β * J)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith









theorem wall_prefactor_bridge {J β : ℝ} (hJ : 0 < J) (hβ : 0 < β) :
    J / (Real.exp (β * J) - 1)
      = (J / (1 - Real.exp (-(β * J)))) * Real.exp (-(β * J)) := by
  have hbJ : 0 < β * J := by positivity
  have h1 : (1 : ℝ) < Real.exp (β * J) := Real.one_lt_exp_iff.mpr hbJ
  have hden : Real.exp (β * J) - 1 ≠ 0 := by linarith
  have hexp : Real.exp (-(β * J)) = (Real.exp (β * J))⁻¹ := by rw [Real.exp_neg]
  have hpos : (0 : ℝ) < Real.exp (β * J) := Real.exp_pos _
  rw [hexp]; field_simp












theorem wall_prefactor_extraction {E : Type*} [Fintype E] (g Cov : E → ℝ) (cR : ℝ)
    (hg : ∀ e, cR ≤ g e) (hCov : ∀ e, 0 ≤ Cov e) :
    cR * ∑ e, Cov e ≤ ∑ e, g e * Cov e :=
  rp_prefactor_extraction g Cov cR hg hCov








theorem wall_russo_extraction {E : Type*} [Fintype E] [Nonempty E]
    (J Cov : E → ℝ) (β : ℝ) (hJ : ∀ e, 0 < J e) (hβ : 0 < β)
    (hCov : ∀ e, 0 ≤ Cov e) :
    ∃ cR : ℝ, 0 < cR ∧ (∀ e, cR ≤ J e / (Real.exp (β * J e) - 1)) ∧
      cR * ∑ e, Cov e ≤ ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e := by
  set g : E → ℝ := fun e => J e / (Real.exp (β * J e) - 1) with hg
  have hgpos : ∀ e, 0 < g e := fun e => wall_prefactor_pos (hJ e) hβ
  obtain ⟨cR, hcRpos, hcRle⟩ := wall_minPrefactor_pos g hgpos
  exact ⟨cR, hcRpos, hcRle, wall_prefactor_extraction g Cov cR hcRle hCov⟩






























theorem wall_russo_prefactor {E : Type*} [Fintype E] [Nonempty E]
    (J Cov : E → ℝ) (β β₀ θ' : ℝ)
    (hJ : ∀ e, 0 < J e) (hβ : 0 < β) (hββ : β ≤ β₀)
    (hCov : ∀ e, 0 ≤ Cov e)
    (hderiv : θ' = ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e) :
    ∃ cR : ℝ, 0 < cR ∧ (∀ e, cR ≤ J e / (Real.exp (β₀ * J e) - 1)) ∧
      cR * ∑ e, Cov e ≤ θ' := by
  
  set g₀ : E → ℝ := fun e => J e / (Real.exp (β₀ * J e) - 1) with hg₀
  have hg₀pos : ∀ e, 0 < g₀ e := fun e =>
    wall_prefactor_pos (hJ e) (lt_of_lt_of_le hβ hββ)
  obtain ⟨cR, hcRpos, hcRle⟩ := wall_minPrefactor_pos g₀ hg₀pos
  refine ⟨cR, hcRpos, hcRle, ?_⟩
  rw [hderiv]
  
  have hcR_le_beta : ∀ e, cR ≤ J e / (Real.exp (β * J e) - 1) := fun e =>
    (hcRle e).trans (wall_prefactor_antitone_beta (hJ e) hβ hββ)
  exact wall_prefactor_extraction (fun e => J e / (Real.exp (β * J e) - 1)) Cov cR
    hcR_le_beta hCov
















theorem wall_russo_lower_bound {E : Type*} [Fintype E] [Nonempty E]
    (J Cov : E → ℝ) (β β₀ θ' : ℝ)
    (hJ : ∀ e, 0 < J e) (hβ : 0 < β) (hββ : β ≤ β₀)
    (hCov : ∀ e, 0 ≤ Cov e)
    (hderiv : θ' = ∑ e, (J e / (Real.exp (β * J e) - 1)) * Cov e) :
    ∃ cR : ℝ, 0 < cR ∧ cR * (∑ e, Cov e) ≤ θ' := by
  obtain ⟨cR, hcRpos, _, hbound⟩ :=
    wall_russo_prefactor J Cov β β₀ θ' hJ hβ hββ hCov hderiv
  exact ⟨cR, hcRpos, hbound⟩

end Walls
end StatMech
