/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











































































import Mathlib
import Code.OSSS.CovLowerBound
import Code.OSSS.Lindeberg
import Code.OSSS.MonotonicOSSS
import Code.Inequalities.OSSS
import Code.Walls.oc2_thetamatch
import Code.Walls.oc3_noproductweight
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
open StatMech.OSSS.CovLowerBound

variable {E : Type*} [Fintype E] [DecidableEq E]


















theorem oc4_allF_match_meanMatch (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ)
    (hall : ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
    ∀ g, expect ν g = Lindeberg.mean μ g :=
  fun g => (oc3_expectAsCubeAt_iff_meanMatch μ hpos hμ1 σ ν g).mp (hall g)



















theorem oc4_allF_match_forces_uncorrelated (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (hall : ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) (e e' : E) (he : e ≠ e') :
    Lindeberg.cov μ (Lindeberg.coord e) (Lindeberg.coord e') = 0 :=
  oc3_match_forces_uncorrelated hν (oc4_allF_match_meanMatch μ hpos hμ1 σ ν hall) e e' he





















theorem oc4_no_product_weight_expectAsCubeAt (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (hcorr : oc3_GenuinelyCorrelated μ) :
    ¬ ∃ ν : E → Bool → ℝ, IsProbWeight ν ∧
        ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f := by
  obtain ⟨e, e', he, hne⟩ := hcorr
  rintro ⟨ν, hν, hall⟩
  exact hne (oc4_allF_match_forces_uncorrelated μ hpos hμ1 σ hν hall e e' he)






theorem oc4_allF_match_not_genuinelyCorrelated (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (hall : ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) :
    ¬ oc3_GenuinelyCorrelated μ := by
  rintro ⟨e, e', he, hne⟩
  exact hne (oc4_allF_match_forces_uncorrelated μ hpos hμ1 σ hν hall e e' he)






theorem oc4_allF_match_iff_weight_eq (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ) :
    (∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f) ↔ (∀ ω, weight ν ω = μ ω) := by
  rw [← oc3_match_iff_weight_eq]
  constructor
  · exact fun hall g => (oc3_expectAsCubeAt_iff_meanMatch μ hpos hμ1 σ ν g).mp (hall g)
  · exact fun hmatch f => (oc3_expectAsCubeAt_iff_meanMatch μ hpos hμ1 σ ν f).mpr (hmatch f)













section FK

open StatMech.OSSS.MonotonicFK














theorem oc4_fk_no_product_weight_expectAsCubeAt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (e e' : Sym2 V) (he : e ≠ e')
    (hfkg : Lindeberg.cov (fkMass G p q) (Lindeberg.coord e) (Lindeberg.coord e') ≠ 0) :
    ¬ ∃ ν : Sym2 V → Bool → ℝ, IsProbWeight ν ∧
        ∀ f, oc2_ExpectAsCubeAt ν (fkMass G p q) (σ : Fin n → Sym2 V) f :=
  oc4_no_product_weight_expectAsCubeAt (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ ⟨e, e', he, hfkg⟩







theorem oc4_fk_allF_match_forces_uncorrelated {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    {ν : Sym2 V → Bool → ℝ} (hν : IsProbWeight ν)
    (hall : ∀ f, oc2_ExpectAsCubeAt ν (fkMass G p q) (σ : Fin n → Sym2 V) f)
    (e e' : Sym2 V) (he : e ≠ e') :
    Lindeberg.cov (fkMass G p q) (Lindeberg.coord e) (Lindeberg.coord e') = 0 :=
  oc4_allF_match_forces_uncorrelated (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ hν hall e e' he

end FK














noncomputable def oc4_posCorrMu : ConfigSpace (Fin 2) → ℝ :=
  fun ω => if ω 0 = ω 1 then (2 : ℝ) / 5 else (1 : ℝ) / 10


theorem oc4_posCorrMu_pos : ∀ ω, 0 < oc4_posCorrMu ω := by
  intro ω; unfold oc4_posCorrMu; split <;> norm_num



theorem oc4_posCorrMu_sum_eq_one : ∑ ω : ConfigSpace (Fin 2), oc4_posCorrMu ω = 1 := by
  have huniv : (Finset.univ : Finset (ConfigSpace (Fin 2)))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
  rw [huniv]
  unfold oc4_posCorrMu
  norm_num [Finset.sum_insert, Finset.mem_insert, Matrix.cons_val_zero, Matrix.cons_val_one]



theorem oc4_posCorrMu_cov_ne_zero :
    Lindeberg.cov oc4_posCorrMu (Lindeberg.coord (0 : Fin 2)) (Lindeberg.coord (1 : Fin 2)) ≠ 0 := by
  unfold Lindeberg.cov Lindeberg.mean Lindeberg.coord oc4_posCorrMu
  have huniv : (Finset.univ : Finset (ConfigSpace (Fin 2)))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by decide
  rw [huniv]
  norm_num [Finset.sum_insert, Finset.mem_insert, Matrix.cons_val_zero, Matrix.cons_val_one]



theorem oc4_posCorrMu_genuinelyCorrelated : oc3_GenuinelyCorrelated oc4_posCorrMu :=
  ⟨0, 1, by decide, oc4_posCorrMu_cov_ne_zero⟩











theorem oc4_no_product_weight_expectAsCubeAt_witness (σ : Fin 2 ≃ Fin 2) :
    ¬ ∃ ν : Fin 2 → Bool → ℝ, IsProbWeight ν ∧
        ∀ f, oc2_ExpectAsCubeAt ν oc4_posCorrMu (σ : Fin 2 → Fin 2) f :=
  oc4_no_product_weight_expectAsCubeAt oc4_posCorrMu oc4_posCorrMu_pos
    oc4_posCorrMu_sum_eq_one σ oc4_posCorrMu_genuinelyCorrelated

end Walls
end StatMech
