/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.OSSS.RevealmentBoxCrossing
import Code.Walls.oc3_core

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.Coding
open StatMech.OSSS.GrandCoupling
open StatMech.OSSS.AdaptMConditional
open StatMech.OSSS.RevealmentBoxCrossing

variable {E : Type*} [Fintype E] [DecidableEq E]


















theorem oc4_revealAsCube_collapse (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) :
    (∫ p, truncInd μ σ f p.1 t ∂((Vcube n).prod (Vcube n)))
      = ∫ U, truncInd μ σ f U t ∂(Vcube n) := by
  rw [integral_prod _ (integrable_truncInd μ σ f t)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro U
  simp only
  rw [integral_const]
  simp






















theorem oc4_revealAsCube (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e = ∑ X, truncIndC σ f X ((σ.symm e : ℕ) + 1) * μ X := by
  unfold revealAdapt
  
  rw [oc4_revealAsCube_collapse μ σ f ((σ.symm e : ℕ) + 1)]
  
  rw [show (fun U => truncInd μ σ f U ((σ.symm e : ℕ) + 1))
        = (fun U => truncIndC σ f (codeMap μ (σ : Fin n → E) U) ((σ.symm e : ℕ) + 1)) from by
    funext U; rw [truncInd_eq_truncIndC]]
  
  rw [oc3_codingLawIntegral μ hpos hμ1 σ (fun X => truncIndC σ f X ((σ.symm e : ℕ) + 1))]











theorem oc4_revealAsCube_mean (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e
      = Lindeberg.mean μ (fun X => truncIndC σ f X ((σ.symm e : ℕ) + 1)) := by
  rw [oc4_revealAsCube μ hpos hμ1 σ f e]
  rfl









theorem oc4_revealAsCube_cubeIntegral (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e
      = ∫ U, truncIndC σ f (codeMap μ (σ : Fin n → E) U) ((σ.symm e : ℕ) + 1) ∂(Vcube n) := by
  rw [oc4_revealAsCube_mean μ hpos hμ1 σ f e]
  exact oc3_expectAsCube_codingFrame μ hpos hμ1 σ
    (fun X => truncIndC σ f X ((σ.symm e : ℕ) + 1))







section FK

open StatMech.OSSS.MonotonicFK










theorem oc4_fk_revealAsCube {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) (e : Sym2 V) :
    revealAdapt (fkMass G p 2) σ f e
      = ∑ X, truncIndC σ f X ((σ.symm e : ℕ) + 1) * fkMass G p 2 X :=
  oc4_revealAsCube (fkMass G p 2) (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num)) σ f e

end FK










theorem oc4_revealAsCube_const (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E) :
    revealAdapt μ σ f e
      = ∑ X ∈ Finset.univ.filter
          (fun X => ((σ.symm e : ℕ) + 1) ≤ stopValC σ f X), μ X := by
  rw [oc4_revealAsCube μ hpos hμ1 σ f e]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro X _
  unfold truncIndC
  by_cases h : ((σ.symm e : ℕ) + 1) ≤ stopValC σ f X
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul]





theorem oc4_revealAsCube_mean_const_one (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    Lindeberg.mean μ (fun X => truncIndC σ f X 0) = 1 := by
  unfold Lindeberg.mean
  rw [show (∑ X, truncIndC σ f X 0 * μ X) = ∑ X, μ X from by
    apply Finset.sum_congr rfl
    intro X _
    unfold truncIndC
    rw [if_pos (Nat.zero_le _), one_mul]]
  exact hμ1

end Walls
end StatMech
