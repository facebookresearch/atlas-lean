/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.OSSS.Coding
import Code.OSSS.GrandCoupling
import Code.OSSS.MonotonicOSSS
import Code.Walls.oc2_codinglawsingle

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls

open StatMech StatMech.OSSS.Coding StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]












noncomputable def oc3_muPMF (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) : PMF (ConfigSpace E) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (μ x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => (hpos x).le), hμ1, ENNReal.ofReal_one])


@[simp] theorem oc3_muPMF_apply (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (x : ConfigSpace E) :
    oc3_muPMF μ hpos hμ1 x = ENNReal.ofReal (μ x) := rfl


theorem oc3_muPMF_toMeasure_singleton (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (x : ConfigSpace E) :
    (oc3_muPMF μ hpos hμ1).toMeasure {x} = ENNReal.ofReal (μ x) := by
  rw [PMF.toMeasure_apply_singleton _ x (measurableSet_singleton x), oc3_muPMF_apply]



















theorem oc3_pushforward_singleton (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    ((Vcube n).map (codeMap μ (σ : Fin n → E))) {x} = ENNReal.ofReal (μ x) := by
  rw [Measure.map_apply (measurable_codeMap μ σ) (measurableSet_singleton x)]
  have hfibre : ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal = μ x :=
    vcube_fibre μ hpos hμ1 σ x
  have hpre : (codeMap μ (σ : Fin n → E)) ⁻¹' {x} = {u | codeMap μ (σ : Fin n → E) u = x} := rfl
  rw [hpre, ← hfibre, ENNReal.ofReal_toReal (measure_ne_top (Vcube n) _)]



















theorem oc3_pushforward_law (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) :
    (Vcube n).map (codeMap μ (σ : Fin n → E)) = (oc3_muPMF μ hpos hμ1).toMeasure := by
  apply Measure.ext_of_singleton
  intro x
  rw [oc3_pushforward_singleton μ hpos hμ1 σ x, oc3_muPMF_toMeasure_singleton μ hpos hμ1 x]





theorem oc3_pushforward_isProbabilityMeasure (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) :
    IsProbabilityMeasure ((Vcube n).map (codeMap μ (σ : Fin n → E))) := by
  rw [oc3_pushforward_law μ hpos hμ1 σ]; infer_instance













theorem oc3_pushforward_apply (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (s : Finset (ConfigSpace E)) :
    ((Vcube n).map (codeMap μ (σ : Fin n → E))) (s : Set (ConfigSpace E))
      = ∑ x ∈ s, ENNReal.ofReal (μ x) := by
  classical
  rw [oc3_pushforward_law μ hpos hμ1 σ]
  rw [PMF.toMeasure_apply _ s.measurableSet]
  rw [tsum_eq_sum (s := s) (by
    intro x hx
    rw [Set.indicator_of_notMem (by simpa using hx)])]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Set.indicator_of_mem (by simpa using hx), oc3_muPMF_apply]










theorem oc3_integral_pushforward (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) :
    ∫ x, g x ∂((Vcube n).map (codeMap μ (σ : Fin n → E))) = ∑ x, g x * μ x := by
  rw [integral_map (measurable_codeMap μ σ).aemeasurable
        (measurable_of_finite g).aestronglyMeasurable]
  exact oc2_coding_law_single μ hpos hμ1 σ g








section FK

open StatMech.OSSS.MonotonicFK











theorem oc3_fk_pushforward_law {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V) :
    (Vcube n).map (codeMap (fkMass G p q) (σ : Fin n → Sym2 V))
      = (oc3_muPMF (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
          (fkMass_sum_eq_one G hp hp1 hq)).toMeasure :=
  oc3_pushforward_law (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ




theorem oc3_fk_pushforward_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (x : ConfigSpace (Sym2 V)) :
    ((Vcube n).map (codeMap (fkMass G p q) (σ : Fin n → Sym2 V))) {x}
      = ENNReal.ofReal (fkMass G p q x) :=
  oc3_pushforward_singleton (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ x

end FK









theorem oc3_pushforward_singleton_empty [IsEmpty E] (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) (σ : Fin 0 ≃ E) (x : ConfigSpace E) :
    ((Vcube 0).map (codeMap μ (σ : Fin 0 → E))) {x} = ENNReal.ofReal (μ x) :=
  oc3_pushforward_singleton μ hpos hμ1 σ x




theorem oc3_pushforward_law_empty [IsEmpty E] (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) (σ : Fin 0 ≃ E) :
    (Vcube 0).map (codeMap μ (σ : Fin 0 → E)) = (oc3_muPMF μ hpos hμ1).toMeasure :=
  oc3_pushforward_law μ hpos hμ1 σ

end Walls
end StatMech
