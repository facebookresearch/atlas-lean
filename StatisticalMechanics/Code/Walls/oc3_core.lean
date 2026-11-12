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
import Code.OSSS.Lindeberg
import Code.Inequalities.OSSS
import Code.Walls.oc2_thetamatch
import Code.Walls.oc3_codinglawintegral
import Code.Walls.oc3_pushforwardlaw
import Code.Walls.oc3_integralmap
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

























theorem oc3_expectAsCube_codingFrame (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    Lindeberg.mean μ f = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) := by
  rw [oc3_codingLawIntegral μ hpos hμ1 σ f]
  rfl










theorem oc3_codingFrame_measurePreserving (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) :
    (Vcube n).map (codeMap μ (σ : Fin n → E)) = (oc3_muPMF μ hpos hμ1).toMeasure :=
  oc3_pushforward_law μ hpos hμ1 σ










theorem oc3_expectAsCube_codingFrame_triple (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    Lindeberg.mean μ f = ∫ x, f x ∂(oc3_codeLaw μ σ)
      ∧ (∫ x, f x ∂(oc3_codeLaw μ σ)) = ∫ u, f (codeMap μ (σ : Fin n → E) u) ∂(Vcube n) := by
  obtain ⟨hcv, hsum⟩ := oc3_integralMap μ hpos hμ1 σ f
  refine ⟨?_, hcv.symm⟩
  rw [hsum]; rfl






















theorem oc3_expectAsCubeAt_iff_meanMatch (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ) (f : ConfigSpace E → ℝ) :
    oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f ↔ expect ν f = Lindeberg.mean μ f := by
  unfold oc2_ExpectAsCubeAt
  rw [oc3_expectAsCube_codingFrame μ hpos hμ1 σ f]





theorem oc3_expectAsCubeAt_of_meanMatch (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (ν : E → Bool → ℝ) (f : ConfigSpace E → ℝ)
    (hmatch : expect ν f = Lindeberg.mean μ f) :
    oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f :=
  (oc3_expectAsCubeAt_iff_meanMatch μ hpos hμ1 σ ν f).mpr hmatch






theorem oc3_expectAsCubeAt_of_const (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    (c : ℝ) :
    oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) (fun _ => c) := by
  refine oc3_expectAsCubeAt_of_meanMatch μ hpos hμ1 σ ν (fun _ => c) ?_
  
  have hexp : expect ν (fun _ => c) = c := by
    rw [show (fun _ : ConfigSpace E => c) = (fun ω => c * (fun _ => (1 : ℝ)) ω) by
      funext ω; rw [mul_one]]
    rw [OSSS.expect_const_mul ν c (fun _ => 1), OSSS.expect_one hν, mul_one]
  have hmean : Lindeberg.mean μ (fun _ => c) = c := by
    unfold Lindeberg.mean
    rw [show (∑ ω, c * μ ω) = c * (∑ ω, μ ω) by rw [Finset.mul_sum]]
    rw [hμ1, mul_one]
  rw [hexp, hmean]





















theorem oc3_no_general_product_frame (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (hcorr : oc3_GenuinelyCorrelated μ) :
    ¬ ∃ ν : E → Bool → ℝ, IsProbWeight ν ∧
        ∀ f, oc2_ExpectAsCubeAt ν μ (σ : Fin n → E) f := by
  rintro ⟨ν, hν, hall⟩
  refine oc3_no_product_weight hcorr ⟨ν, hν, ?_⟩
  intro g
  exact (oc3_expectAsCubeAt_iff_meanMatch μ hpos hμ1 σ ν g).mp (hall g)








section FK

open StatMech.OSSS.MonotonicFK











theorem oc3_fk_expectAsCube_codingFrame {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) :
    Lindeberg.mean (fkMass G p q) f
      = ∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n) :=
  oc3_expectAsCube_codingFrame (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ f








theorem oc3_fk_codingFrame_measurePreserving {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V) :
    (Vcube n).map (codeMap (fkMass G p q) (σ : Fin n → Sym2 V))
      = (oc3_muPMF (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
          (fkMass_sum_eq_one G hp hp1 hq)).toMeasure :=
  oc3_codingFrame_measurePreserving (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ

end FK








theorem oc3_expectAsCube_codingFrame_const (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (c : ℝ) :
    Lindeberg.mean μ (fun _ => c) = ∫ _u, c ∂(Vcube n) :=
  oc3_expectAsCube_codingFrame μ hpos hμ1 σ (fun _ => c)




theorem oc3_expectAsCubeAt_empty [IsEmpty E] (μ : ConfigSpace E → ℝ) (ν : E → Bool → ℝ)
    (σ : Fin 0 ≃ E) (f : ConfigSpace E → ℝ) :
    oc2_ExpectAsCubeAt ν μ (σ : Fin 0 → E) f :=
  oc2_expectAsCubeAt_empty μ ν σ f

end Walls
end StatMech
