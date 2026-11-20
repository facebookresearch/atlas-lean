/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































































import Mathlib
import Code.OSSS.GrandCoupling
import Code.OSSS.Lindeberg
import Code.OSSS.CovLowerBound
import Code.Inequalities.OSSS
import Code.Walls.oc_core
import Code.Walls.oc2_covedgeascube
import Code.Walls.oc2_thetamatch
import Code.Walls.oc2_codinglawsingle
import Code.Walls.oc2_coordreadmatch

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

variable {E : Type*} [Fintype E] [DecidableEq E]











noncomputable def oc2_cubeCovSum (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (f : ConfigSpace E → ℝ) : ℝ :=
  ∑ e, oc2_cubeCov μ σ f (CovLowerBound.coordI e)
















theorem oc2_corr_covSum_eq_cubeCovSum (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    (∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e))
      = oc2_cubeCovSum μ (σ : Fin n → E) f :=
  Finset.sum_congr rfl (fun e _ => oc2_cov_edge_as_cube_coordI μ hpos hμ1 σ f e)








theorem oc2_corr_mean_eq_cubeIntegral (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) :=
  (oc2_cubeIntegral_eq_mean μ hpos hμ1 σ f).symm
















theorem oc2_codingCovBridge_cubeFrame (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    (∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e)) = oc2_cubeCovSum μ (σ : Fin n → E) f
      ∧ Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) :=
  ⟨oc2_corr_covSum_eq_cubeCovSum μ hpos hμ1 σ f,
   oc2_corr_mean_eq_cubeIntegral μ hpos hμ1 σ f⟩






















def oc2_SumCovMatch (μ : ConfigSpace E → ℝ) (ν : E → Bool → ℝ) {n : ℕ} (σ : Fin n → E)
    (f : ConfigSpace E → ℝ) : Prop :=
  (∑ e, cov ν (CovLowerBound.coordI e) f) = oc2_cubeCovSum μ σ f















theorem oc2_codingCovBridge_of_residue (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ) (f : ConfigSpace E → ℝ)
    (hSum : oc2_SumCovMatch μ ν (σ : Fin n → E) f)
    (hθ : oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
    oc_CodingCovBridge (ν := ν) f (Lindeberg.mean μ f)
        (∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e)) := by
  refine ⟨?_, ?_⟩
  · 
    rw [oc2_corr_covSum_eq_cubeCovSum μ hpos hμ1 σ f]
    exact hSum.symm
  · 
    exact oc2_theta_match μ hpos hμ1 σ ν f hθ






















theorem oc2_correlated_covLowerBound_cubeFrame (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (N c₀ D : ℝ)
    (hcube : N * c₀ * ((∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n))
        * (1 - ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n)))
      ≤ D * oc2_cubeCovSum μ (σ : Fin n → E) f) :
    N * c₀ * (Lindeberg.mean μ f * (1 - Lindeberg.mean μ f))
      ≤ D * ∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e) := by
  rw [oc2_corr_mean_eq_cubeIntegral μ hpos hμ1 σ f,
      oc2_corr_covSum_eq_cubeCovSum μ hpos hμ1 σ f]
  exact hcube










theorem oc2_codingCovBridge_cubeFrame_refl (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (f : ConfigSpace E → ℝ) :
    (oc2_cubeCovSum μ σ f) = oc2_cubeCovSum μ σ f
      ∧ (∫ u, f (codeMap μ σ u) ∂(Vcube n)) = ∫ u, f (codeMap μ σ u) ∂(Vcube n) :=
  ⟨rfl, rfl⟩






theorem oc2_sumCovMatch_empty [IsEmpty E] (μ : ConfigSpace E → ℝ) (ν : E → Bool → ℝ)
    (σ : Fin 0 → E) (f : ConfigSpace E → ℝ) :
    oc2_SumCovMatch μ ν σ f := by
  unfold oc2_SumCovMatch oc2_cubeCovSum
  simp only [Finset.univ_eq_empty, Finset.sum_empty]







theorem oc2_codingCovBridge_of_residue_empty [IsEmpty E] (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) (σ : Fin 0 ≃ E) (ν : E → Bool → ℝ)
    (f : ConfigSpace E → ℝ) :
    oc_CodingCovBridge (ν := ν) f (Lindeberg.mean μ f)
        (∑ e, Lindeberg.cov μ f (CovLowerBound.coordI e)) :=
  oc2_codingCovBridge_of_residue μ hpos hμ1 σ ν f
    (oc2_sumCovMatch_empty μ ν (σ : Fin 0 → E) f)
    (oc2_expectAsCubeAt_empty μ ν σ f)









section FK

open StatMech.OSSS.MonotonicFK











theorem oc2_fk_codingCovBridge_cubeFrame {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) :
    (∑ e, Lindeberg.cov (fkMass G p q) f (CovLowerBound.coordI e))
        = oc2_cubeCovSum (fkMass G p q) (σ : Fin n → Sym2 V) f
      ∧ Lindeberg.mean (fkMass G p q) f
        = ∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n) :=
  oc2_codingCovBridge_cubeFrame (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ f







theorem oc2_fk_codingCovBridge_of_residue {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (ν : Sym2 V → Bool → ℝ) (f : ConfigSpace (Sym2 V) → ℝ)
    (hSum : oc2_SumCovMatch (fkMass G p q) ν (σ : Fin n → Sym2 V) f)
    (hθ : oc2_ExpectAsCubeAt ν (fkMass G p q) (σ : Fin n → Sym2 V) f) :
    oc_CodingCovBridge (ν := ν) f (Lindeberg.mean (fkMass G p q) f)
        (∑ e, Lindeberg.cov (fkMass G p q) f (CovLowerBound.coordI e)) :=
  oc2_codingCovBridge_of_residue (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ ν f hSum hθ

end FK

end Walls
end StatMech
