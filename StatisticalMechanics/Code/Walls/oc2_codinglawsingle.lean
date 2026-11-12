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

namespace StatMech
namespace Walls

open StatMech.OSSS.Coding StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]












theorem oc2_coding_fibre_mass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal = μ x :=
  vcube_fibre μ hpos hμ1 σ x


















theorem oc2_coding_law_single (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) :
    ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∑ x, g x * μ x := by
  
  have hms : ∀ x : ConfigSpace E,
      MeasurableSet {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x} :=
    fun x => (measurable_codeMap μ σ) (measurableSet_singleton x)
  
  have hpt : (fun u => g (codeMap μ (σ : Fin n → E) u))
      = (fun u => ∑ x, g x
          * (Set.indicator {u | codeMap μ (σ : Fin n → E) u = x} (fun _ => (1 : ℝ)) u)) := by
    funext u
    rw [Finset.sum_eq_single (codeMap μ (σ : Fin n → E) u)]
    · rw [Set.indicator_of_mem
        (by simp : u ∈ {u' | codeMap μ (σ : Fin n → E) u' = codeMap μ (σ : Fin n → E) u})]; ring
    · intro x _ hx
      rw [Set.indicator_of_notMem
        (by simp only [Set.mem_setOf_eq]; exact fun h => hx h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hpt, integral_finsetSum]
  · 
    apply Finset.sum_congr rfl
    intro x _
    rw [integral_const_mul, integral_indicator_const (1 : ℝ) (hms x), smul_eq_mul, mul_one]
    rw [show (Vcube n).real {u | codeMap μ (σ : Fin n → E) u = x}
        = ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal from rfl]
    rw [oc2_coding_fibre_mass μ hpos hμ1 σ x]
  · 
    intro x _
    exact Integrable.const_mul (Integrable.indicator (integrable_const 1) (hms x)) _












theorem oc2_coding_law_single_expect (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) :
    ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∑ x, g x * μ x :=
  oc2_coding_law_single μ hpos hμ1 σ g




theorem oc2_coding_law_const_one (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) :
    ∫ _u, (1 : ℝ) ∂(Vcube n) = 1 := by
  have h := oc2_coding_law_single μ hpos hμ1 σ (fun _ => (1 : ℝ))
  simp only [one_mul] at h
  rw [h, hμ1]





theorem oc2_coding_law_indicator (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    ∫ u, (if codeMap μ (σ : Fin n → E) u = x then (1 : ℝ) else 0) ∂(Vcube n) = μ x := by
  have h := oc2_coding_law_single μ hpos hμ1 σ (fun y => if y = x then (1 : ℝ) else 0)
  
  rw [show (fun u => (if codeMap μ (σ : Fin n → E) u = x then (1 : ℝ) else 0))
        = (fun u => (fun y => if y = x then (1 : ℝ) else 0) (codeMap μ (σ : Fin n → E) u)) from rfl]
  rw [h]
  
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl, one_mul]
  · intro y _ hy; rw [if_neg hy, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end Walls
end StatMech
