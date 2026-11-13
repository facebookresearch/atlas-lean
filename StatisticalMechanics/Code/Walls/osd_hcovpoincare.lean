/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Code.OSSS.FKSharpnessAssembly
import Code.OSSS.MonotoneOSSSAssembly
import Code.OSSS.RevealmentBoundAssembly
import Code.OSSS.LindebergTree

open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace Walls

open StatMech.OSSS
open StatMech.OSSS.SharpnessFK
open StatMech.FK
open StatMech.OSSS.MonotonicFK
open StatMech.OSSS.AdaptDisintegration
open StatMech.OSSS.AdaptMConditional
open StatMech.OSSS.RevealmentBoundAssembly

variable {V : Type*} [Fintype V] [DecidableEq V]





















theorem osd_hcovPoincare (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A) :
    fkProbOf G p 2 A * (1 - fkProbOf G p 2 A)
      ≤ ∑ e, fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e) :=
  fk_poincare_indicator G hp hp1 (by norm_num : (1 : ℝ) ≤ 2) A hA
























theorem osd_hcovPoincare_var (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {n : ℕ} (σ : Fin n ≃ Sym2 V)
    {f : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var (fkMass G p 2) f
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
  
  have hpos : ∀ ω, 0 < fkMass G p 2 ω := fun ω => fkMass_pos G hp hp1 (by norm_num) ω
  have hμ1 : ∑ ω, fkMass G p 2 ω = 1 := fkMass_sum_eq_one G hp hp1 (by norm_num)
  have hFKG : FKGLatticeCondition (fkMass G p 2) :=
    FK.fkProb_FKGLatticeCondition G hp hp1 (by norm_num)
  
  have hsharp := osss_fk_q2_sharp G hp hp1 σ hf hf0 hf1
  refine hsharp.trans ?_
  
  apply Finset.sum_le_sum
  intro e _
  have hcovnn : 0 ≤ Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
    LindebergTree.cov_coord_nonneg hpos hμ1 hFKG hf e
  calc revealAdapt (fkMass G p 2) σ f e * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e)
      ≤ 1 * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
        mul_le_mul_of_nonneg_right (revealAdapt_le_one (fkMass G p 2) σ f e) hcovnn
    _ = Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := one_mul _











theorem osd_hcovPoincare_indicator (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A) :
    Lindeberg.mean (fkMass G p 2) (A.indicator (fun _ => (1 : ℝ)))
        * (1 - Lindeberg.mean (fkMass G p 2) (A.indicator (fun _ => (1 : ℝ))))
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2)
          (A.indicator (fun _ => (1 : ℝ))) (Lindeberg.coord e) := by
  classical
  have hf : Monotone (A.indicator (fun _ => (1 : ℝ))) := hA.indicator_monotone
  have hf0 : 0 ≤ A.indicator (fun _ => (1 : ℝ)) := StatMech.indicator_nonneg' A
  have hf1 : ∀ ω, A.indicator (fun _ => (1 : ℝ)) ω ≤ 1 := fun ω => by
    rw [Set.indicator_apply]; split_ifs <;> norm_num
  have hvar : Lindeberg.var (fkMass G p 2) (A.indicator (fun _ => (1 : ℝ)))
      = Lindeberg.mean (fkMass G p 2) (A.indicator (fun _ => (1 : ℝ)))
          * (1 - Lindeberg.mean (fkMass G p 2) (A.indicator (fun _ => (1 : ℝ)))) :=
    lind_var_indicator (A.indicator (fun _ => (1 : ℝ)))
      (fun ω => by
        by_cases h : ω ∈ A
        · right; rw [Set.indicator_of_mem h]
        · left; rw [Set.indicator_of_notMem h])
  rw [← hvar]
  exact osd_hcovPoincare_var G hp hp1 σ hf hf0 hf1

end Walls
end StatMech
