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











theorem oc3_fibre_eq_rawbox (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (x : ConfigSpace E) :
    {u : Fin n → ℝ | codeMap μ (σ : Fin n → E) u = x}
      = Set.univ.pi (fun t => rawInterval μ (σ : Fin n → E) x t) :=
  codeMap_fibre_eq_rawbox μ σ x












theorem oc3_rawInterval_marginal (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) {n : ℕ}
    (σ : Fin n ≃ E) (x : ConfigSpace E) (t : Fin n) :
    (volume.restrict (Set.Icc (0 : ℝ) 1) (rawInterval μ (σ : Fin n → E) x t)).toReal
      = condProbBit μ (prefixSet (σ : Fin n → E) (t : ℕ)) x
          ((σ : Fin n → E) t) (x ((σ : Fin n → E) t)) :=
  vcube_rawInterval μ hpos (σ : Fin n → E) x t









theorem oc3_marginals_telescope (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    (∏ t : Fin n, condProbBit μ (prefixSet (σ : Fin n → E) (t : ℕ)) x
        ((σ : Fin n → E) t) (x ((σ : Fin n → E) t)))
      = μ x :=
  codeProb_eq_mass μ hpos hμ1 σ x














theorem oc3_vcube_fibre_prod (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) {n : ℕ}
    (σ : Fin n ≃ E) (x : ConfigSpace E) :
    ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal
      = ∏ t : Fin n, condProbBit μ (prefixSet (σ : Fin n → E) (t : ℕ)) x
          ((σ : Fin n → E) t) (x ((σ : Fin n → E) t)) := by
  
  rw [oc3_fibre_eq_rawbox μ σ x]
  
  unfold Vcube
  
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  
  apply Finset.prod_congr rfl
  intro t _
  exact oc3_rawInterval_marginal μ hpos σ x t


















theorem oc3_vcube_fibre (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal = μ x := by
  
  rw [oc3_vcube_fibre_prod μ hpos σ x]
  
  exact oc3_marginals_telescope μ hpos hμ1 σ x











theorem oc3_vcube_total_mass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) :
    (∑ x : ConfigSpace E,
        ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal) = 1 := by
  rw [← hμ1]
  apply Finset.sum_congr rfl
  intro x _
  exact oc3_vcube_fibre μ hpos hμ1 σ x

end Walls
end StatMech
