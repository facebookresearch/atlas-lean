/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Code.OSSS.FKQ2SharpUncond

open scoped BigOperators
open MeasureTheory

namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability
open StatMech.OSSS.MonotonicFK

variable {E : Type*} [Fintype E] [DecidableEq E]






















theorem osss_onestep_cov_bound {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    AdaptStepCovBound μ σ f := by
  have hf0' : ∀ ω, (0 : ℝ) ≤ f ω := fun ω => hf0 ω
  have hfC : ∀ ω, |f ω| ≤ 1 := fun ω => by
    rw [abs_le]; exact ⟨by linarith [hf0' ω], hf1 ω⟩
  
  have hTCL : acp_TailCondLaw μ σ f := cmn_tailCondLaw hpos hμ1 hmono σ hf hfC
  
  have hBBB : AdaptCondBBB μ σ f := otc_adaptCondBBB_of_tailCondLaw σ hfC hTCL
  
  exact adsD_adaptStepCovBound_of_condBBB hpos hmono σ hf hfC hBBB
















theorem osss_monotone_sharp {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f
      ≤ ∑ e, revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e) :=
  tree_osss_sharp_unconditional hpos hμ1 σ hf0 hf1
    (osss_onestep_cov_bound hpos hμ1 hmono σ hf hf0 hf1)



section FK

variable {V : Type*} [Fintype V] [DecidableEq V]













theorem osss_fk_q2_sharp (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) {n : ℕ} (σ : Fin n ≃ Sym2 V)
    {f : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var (fkMass G p 2) f
      ≤ ∑ e, revealAdapt (fkMass G p 2) σ f e
          * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
  osss_monotone_sharp
    (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num))
    (fkMass_isMonotonic G hp hp1 (by norm_num)) σ hf hf0 hf1

end FK

end AdaptDisintegration

end OSSS

end StatMech
