/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.OSSS.Coding
import Code.OSSS.GrandCoupling
import Code.OSSS.Lindeberg
import Code.OSSS.MonotonicOSSS
import Code.Inequalities.OSSS
import Code.Walls.oc3_codinglawintegral
import Code.Walls.oc3_noproductweight

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






















theorem oc4_codingFrame (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) := by
  rw [oc3_codingLawIntegral μ hpos hμ1 σ f]
  rfl







theorem oc4_codingFrame_symm (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    (∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n)) = Lindeberg.mean μ f :=
  (oc4_codingFrame μ hpos hμ1 σ f).symm












theorem oc4_codingFrame_indicator (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (x : ConfigSpace E) :
    μ x = ∫ u, (if codeMap μ (σ : Fin n → E) u = x then (1 : ℝ) else 0) ∂(Vcube n) :=
  (oc3_codingLawIntegral_indicator μ hpos hμ1 σ x).symm



theorem oc4_codingFrame_one (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) :
    (1 : ℝ) = ∫ _u, (1 : ℝ) ∂(Vcube n) :=
  (oc3_codingLawIntegral_const_one μ hpos hμ1 σ).symm




theorem oc4_codingFrame_const (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (c : ℝ) :
    Lindeberg.mean μ (fun _ => c) = ∫ _u, c ∂(Vcube n) :=
  oc4_codingFrame μ hpos hμ1 σ (fun _ => c)







theorem oc4_codingFrame_linear (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (a b : ℝ) (f g : ConfigSpace E → ℝ) :
    Lindeberg.mean μ (fun ω => a * f ω + b * g ω)
      = ∫ u, (a * f (codeMap μ (σ : Fin n → E) u) + b * g (codeMap μ (σ : Fin n → E) u))
          ∂(Vcube n) :=
  oc4_codingFrame μ hpos hμ1 σ (fun ω => a * f ω + b * g ω)























theorem oc4_codingFrame_noProductWeight (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (hcorr : oc3_GenuinelyCorrelated μ) :
    (¬ ∃ ν : E → Bool → ℝ, IsProbWeight ν ∧ ∀ g, expect ν g = Lindeberg.mean μ g)
      ∧ (∀ f, Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n)) := by
  refine ⟨oc3_no_product_weight hcorr, fun f => oc4_codingFrame μ hpos hμ1 σ f⟩








section FK

open StatMech.OSSS.MonotonicFK











theorem oc4_cf_fk_codingFrame {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) :
    Lindeberg.mean (fkMass G p q) f
      = ∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n) :=
  oc4_codingFrame (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ f







theorem oc4_cf_fk_codingFrame_indicator {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (x : ConfigSpace (Sym2 V)) :
    fkMass G p q x
      = ∫ u, (if codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u = x then (1 : ℝ) else 0)
          ∂(Vcube n) :=
  oc4_codingFrame_indicator (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ x

end FK

end Walls
end StatMech
