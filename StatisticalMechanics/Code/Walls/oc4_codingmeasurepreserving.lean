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
import Code.Walls.oc3_pushforwardlaw
import Code.Walls.oc3_integralmap

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace StatMech
namespace Walls

open StatMech.OSSS.Coding StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]


























theorem oc4_coding_measurePreserving (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) :
    MeasurePreserving (codeMap μ (σ : Fin n → E)) (Vcube n)
      (oc3_muPMF μ hpos hμ1).toMeasure :=
  ⟨measurable_codeMap μ σ, oc3_pushforward_law μ hpos hμ1 σ⟩










theorem oc4_codingMeasurePreserving_to_codeLaw (μ : ConfigSpace E → ℝ) {n : ℕ}
    (σ : Fin n ≃ E) :
    MeasurePreserving (codeMap μ (σ : Fin n → E)) (Vcube n) (oc3_codeLaw μ σ) :=
  ⟨measurable_codeMap μ σ, rfl⟩















theorem oc4_coding_preimage_mass (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (s : Set (ConfigSpace E)) :
    (Vcube n) (codeMap μ (σ : Fin n → E) ⁻¹' s) = (oc3_muPMF μ hpos hμ1).toMeasure s :=
  (oc4_coding_measurePreserving μ hpos hμ1 σ).measure_preimage
    (MeasurableSet.of_discrete (s := s)).nullMeasurableSet









theorem oc4_coding_preimage_singleton (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    (Vcube n) (codeMap μ (σ : Fin n → E) ⁻¹' {x}) = ENNReal.ofReal (μ x) := by
  rw [oc4_coding_preimage_mass μ hpos hμ1 σ {x}, oc3_muPMF_toMeasure_singleton μ hpos hμ1 x]


















theorem oc4_coding_measurePreserving_integral (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) :
    ∫ x, g x ∂((oc3_muPMF μ hpos hμ1).toMeasure)
      = ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n)
    ∧ ∫ x, g x ∂((oc3_muPMF μ hpos hμ1).toMeasure) = ∑ x, g x * μ x := by
  
  have hpf : (oc3_muPMF μ hpos hμ1).toMeasure = oc3_codeLaw μ σ :=
    (oc3_pushforward_law μ hpos hμ1 σ).symm
  rw [hpf]
  refine ⟨(oc3_integral_map μ σ g).symm, ?_⟩
  exact oc3_integral_codeLaw_eq_sum μ hpos hμ1 σ g








section FK

open StatMech.OSSS.MonotonicFK











theorem oc4_fk_coding_measurePreserving {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V) :
    MeasurePreserving (codeMap (fkMass G p q) (σ : Fin n → Sym2 V)) (Vcube n)
      (oc3_muPMF (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
        (fkMass_sum_eq_one G hp hp1 hq)).toMeasure :=
  oc4_coding_measurePreserving (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ





theorem oc4_fk_coding_preimage_mass {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (s : Set (ConfigSpace (Sym2 V))) :
    (Vcube n) (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) ⁻¹' s)
      = (oc3_muPMF (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
          (fkMass_sum_eq_one G hp hp1 hq)).toMeasure s :=
  oc4_coding_preimage_mass (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ s

end FK










theorem oc4_coding_target_isProbabilityMeasure (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) :
    IsProbabilityMeasure ((oc3_muPMF μ hpos hμ1).toMeasure) :=
  inferInstance




theorem oc4_coding_preimage_univ (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) :
    (Vcube n) (codeMap μ (σ : Fin n → E) ⁻¹' (Set.univ)) = 1 := by
  rw [oc4_coding_preimage_mass μ hpos hμ1 σ Set.univ]
  exact (oc4_coding_target_isProbabilityMeasure μ hpos hμ1).measure_univ




theorem oc4_coding_measurePreserving_empty [IsEmpty E] (μ : ConfigSpace E → ℝ)
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) (σ : Fin 0 ≃ E) :
    MeasurePreserving (codeMap μ (σ : Fin 0 → E)) (Vcube 0)
      (oc3_muPMF μ hpos hμ1).toMeasure :=
  oc4_coding_measurePreserving μ hpos hμ1 σ

end Walls
end StatMech
