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
import Code.Walls.oc2_thetamatch
import Code.Walls.oc2_core
import Code.Walls.oc3_codinglawintegral
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
open StatMech.OSSS.MonotonicFK

variable {V : Type*} [Fintype V] [DecidableEq V]





















theorem oc4_fk_codingFrame (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) :
    Lindeberg.mean (fkMass G p q) f
      = ∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n) :=
  oc3_fk_expectAsCube_codingFrame G hp hp1 hq σ f









theorem oc4_fk_codingFrame_sum (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) :
    (∑ x, f x * fkMass G p q x)
      = ∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n) := by
  have h := oc4_fk_codingFrame G hp hp1 hq σ f
  rwa [Lindeberg.mean] at h














theorem oc4_fk_codingFrame_measurePreserving (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V) :
    (Vcube n).map (codeMap (fkMass G p q) (σ : Fin n → Sym2 V))
      = (oc3_muPMF (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
          (fkMass_sum_eq_one G hp hp1 hq)).toMeasure :=
  oc3_fk_codingFrame_measurePreserving G hp hp1 hq σ















theorem oc4_fk_codingFrame_indicator (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (x : ConfigSpace (Sym2 V)) :
    ∫ u, (if codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u = x then (1 : ℝ) else 0)
        ∂(Vcube n)
      = fkMass G p q x :=
  oc3_codingLawIntegral_indicator (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ x





theorem oc4_fk_codingFrame_total_mass (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V) :
    ∫ _u, (1 : ℝ) ∂(Vcube n) = 1 :=
  oc3_codingLawIntegral_const_one (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ


























theorem oc4_fk_correlated_covLowerBound_cubeFrame (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (f : ConfigSpace (Sym2 V) → ℝ) (N c₀ D : ℝ)
    (hcube : N * c₀ * ((∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n))
        * (1 - ∫ u, f (codeMap (fkMass G p q) (σ : Fin n → Sym2 V) u) ∂(Vcube n)))
      ≤ D * oc2_cubeCovSum (fkMass G p q) (σ : Fin n → Sym2 V) f) :
    N * c₀ * (Lindeberg.mean (fkMass G p q) f * (1 - Lindeberg.mean (fkMass G p q) f))
      ≤ D * ∑ e, Lindeberg.cov (fkMass G p q) f (CovLowerBound.coordI e) :=
  oc2_correlated_covLowerBound_cubeFrame (fkMass G p q) (fun ω => fkMass_pos G hp hp1 hq ω)
    (fkMass_sum_eq_one G hp hp1 hq) σ f N c₀ D hcube









theorem oc4_fk_codingFrame_const (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {n : ℕ} (σ : Fin n ≃ Sym2 V) (c : ℝ) :
    Lindeberg.mean (fkMass G p q) (fun _ => c)
      = ∫ _u, c ∂(Vcube n) :=
  oc4_fk_codingFrame G hp hp1 hq σ (fun _ => c)





theorem oc4_fk_codingFrame_empty (G : SimpleGraph V) [DecidableRel G.Adj]
    [IsEmpty (Sym2 V)] {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (σ : Fin 0 ≃ Sym2 V) (f : ConfigSpace (Sym2 V) → ℝ) :
    Lindeberg.mean (fkMass G p q) f
      = ∫ u, f (codeMap (fkMass G p q) (σ : Fin 0 → Sym2 V) u) ∂(Vcube 0) :=
  oc4_fk_codingFrame G hp hp1 hq σ f

end Walls
end StatMech
