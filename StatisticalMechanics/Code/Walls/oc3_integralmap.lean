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

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace Walls

open StatMech.OSSS.Coding StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]











theorem oc3_measurable_codeMap (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) :
    Measurable (fun u : Fin n → ℝ => codeMap μ (σ : Fin n → E) u) :=
  measurable_codeMap μ σ










noncomputable def oc3_codeLaw (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) :
    Measure (ConfigSpace E) :=
  Measure.map (codeMap μ (σ : Fin n → E)) (Vcube n)



instance oc3_codeLaw_isProbabilityMeasure (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) :
    IsProbabilityMeasure (oc3_codeLaw μ σ) := by
  unfold oc3_codeLaw
  exact Measure.isProbabilityMeasure_map (measurable_codeMap μ σ).aemeasurable
















theorem oc3_codeLaw_apply (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    (oc3_codeLaw μ σ) {x} = ENNReal.ofReal (μ x) := by
  unfold oc3_codeLaw
  rw [Measure.map_apply (measurable_codeMap μ σ) (measurableSet_singleton x)]
  have hpre : (codeMap μ (σ : Fin n → E)) ⁻¹' {x}
      = {u | codeMap μ (σ : Fin n → E) u = x} := by
    ext u; simp [Set.mem_preimage]
  rw [hpre]
  
  
  have hfin : (Vcube n) {u | codeMap μ (σ : Fin n → E) u = x} ≠ ⊤ :=
    (measure_ne_top (Vcube n) _)
  have htoReal : ((Vcube n) {u | codeMap μ (σ : Fin n → E) u = x}).toReal = μ x :=
    vcube_fibre μ hpos hμ1 σ x
  rw [← htoReal, ENNReal.ofReal_toReal hfin]








theorem oc3_codeLaw_real_singleton (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    (oc3_codeLaw μ σ).real {x} = μ x := by
  unfold oc3_codeLaw Measure.real
  rw [Measure.map_apply (measurable_codeMap μ σ) (measurableSet_singleton x)]
  have hpre : (codeMap μ (σ : Fin n → E)) ⁻¹' {x}
      = {u | codeMap μ (σ : Fin n → E) u = x} := by
    ext u; simp [Set.mem_preimage]
  rw [hpre]
  exact vcube_fibre μ hpos hμ1 σ x
















theorem oc3_integral_map (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) :
    ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∫ x, g x ∂(oc3_codeLaw μ σ) := by
  unfold oc3_codeLaw
  rw [integral_map (measurable_codeMap μ σ).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable]
















theorem oc3_integral_codeLaw_eq_sum (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) :
    ∫ x, g x ∂(oc3_codeLaw μ σ) = ∑ x, g x * μ x := by
  rw [integral_fintype (μ := oc3_codeLaw μ σ) (f := g) Integrable.of_finite]
  apply Finset.sum_congr rfl
  intro x _
  rw [oc3_codeLaw_real_singleton μ hpos hμ1 σ x, smul_eq_mul, mul_comm]
















theorem oc3_integralMap (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) :
    ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∫ x, g x ∂(oc3_codeLaw μ σ)
      ∧ ∫ x, g x ∂(oc3_codeLaw μ σ) = ∑ x, g x * μ x := by
  exact ⟨oc3_integral_map μ σ g, oc3_integral_codeLaw_eq_sum μ hpos hμ1 σ g⟩










theorem oc3_integralMap_eq_sum (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) :
    ∫ u, g (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) = ∑ x, g x * μ x := by
  rw [oc3_integral_map μ σ g, oc3_integral_codeLaw_eq_sum μ hpos hμ1 σ g]









theorem oc3_codeLaw_const_one (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) :
    ∫ _x, (1 : ℝ) ∂(oc3_codeLaw μ σ) = 1 := by
  rw [oc3_integral_codeLaw_eq_sum μ hpos hμ1 σ (fun _ => (1 : ℝ))]
  simp only [one_mul]; exact hμ1




theorem oc3_codeLaw_indicator (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    ∫ y, (if y = x then (1 : ℝ) else 0) ∂(oc3_codeLaw μ σ) = μ x := by
  rw [oc3_integral_codeLaw_eq_sum μ hpos hμ1 σ (fun y => if y = x then (1 : ℝ) else 0)]
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl, one_mul]
  · intro y _ hy; rw [if_neg hy, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h








section FK

open StatMech.OSSS.MonotonicFK







theorem oc3_fk_integralMap {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (g : ConfigSpace (Sym2 V) → ℝ) :
    (∫ u, g (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n)
        = ∫ x, g x ∂(oc3_codeLaw (fkMass G p q) σ))
      ∧ (∫ x, g x ∂(oc3_codeLaw (fkMass G p q) σ) = ∑ x, g x * fkMass G p q x) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact oc3_integralMap (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0) σ g





theorem oc3_fk_codeLaw_apply {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (x : ConfigSpace (Sym2 V)) :
    (oc3_codeLaw (fkMass G p q) σ) {x} = ENNReal.ofReal (fkMass G p q x) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  exact oc3_codeLaw_apply (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq0 ω)
    (fkMass_sum_eq_one G hp hp1 hq0) σ x

end FK

end Walls
end StatMech
