/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.OSSS.Coding
import Code.OSSS.GrandCoupling

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace StatMech
namespace Walls

open StatMech.OSSS.Coding StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]













theorem oc3_codeMap_fibre_eq_iInter (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (x : ConfigSpace E) :
    {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x}
      = ⋂ t : Fin n, {u : Fin n → ℝ |
          x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  exact codeMap_eq_iff μ σ x u










theorem oc3_codeMap_fibre_coord_eq_halfLine (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (x : ConfigSpace E) (t : Fin n) :
    {u : Fin n → ℝ | x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)}
      = (if x ((σ : Fin n → E) t)
          then {u : Fin n → ℝ | u t ≥ thr μ (σ : Fin n → E) x t}
          else {u : Fin n → ℝ | u t < thr μ (σ : Fin n → E) x t}) := by
  by_cases hbit : x ((σ : Fin n → E) t)
  · simp only [hbit, if_true]
    ext u
    simp only [Set.mem_setOf_eq, hbit]
    constructor
    · intro h; have := h.symm; rwa [decide_eq_true_eq] at this
    · intro h; symm; rwa [decide_eq_true_eq]
  · have hbit' : x ((σ : Fin n → E) t) = false := by
      cases h : x ((σ : Fin n → E) t)
      · rfl
      · exact absurd h hbit
    simp only [hbit, Bool.false_eq_true, if_false]
    ext u
    simp only [Set.mem_setOf_eq, hbit']
    constructor
    · intro h; rw [eq_comm, decide_eq_false_iff_not, not_le] at h; exact h
    · intro h; symm; rw [decide_eq_false_iff_not, not_le]; exact h




theorem oc3_measurableSet_codeMap_fibre_coord (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (x : ConfigSpace E) (t : Fin n) :
    MeasurableSet
      {u : Fin n → ℝ | x ((σ : Fin n → E) t) = decide (u t ≥ thr μ (σ : Fin n → E) x t)} := by
  rw [oc3_codeMap_fibre_coord_eq_halfLine μ σ x t]
  by_cases hbit : x ((σ : Fin n → E) t)
  · simp only [hbit, if_true]
    exact measurableSet_le measurable_const (measurable_pi_apply t)
  · simp only [hbit, Bool.false_eq_true, if_false]
    exact measurableSet_lt (measurable_pi_apply t) measurable_const






theorem oc3_measurableSet_codeMap_fibre (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) (x : ConfigSpace E) :
    MeasurableSet {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x} := by
  rw [oc3_codeMap_fibre_eq_iInter μ σ x]
  exact MeasurableSet.iInter (fun t => oc3_measurableSet_codeMap_fibre_coord μ σ x t)







theorem oc3_codemap_measurable (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) :
    Measurable (fun u : Fin n → ℝ => codeMap μ (σ : Fin n → E) u) := by
  apply measurable_to_countable'
  intro x
  exact oc3_measurableSet_codeMap_fibre μ σ x





theorem oc3_measurable_g_codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) :
    Measurable (fun u : Fin n → ℝ => g (codeMap μ (σ : Fin n → E) u)) :=
  (measurable_of_finite g).comp (oc3_codemap_measurable μ σ)

end Walls
end StatMech
