/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































import Code.OSSS.AdaptDisintegration
import Code.OSSS.AdaptCondReduction
import Code.OSSS.CrossMonotone

open scoped BigOperators
open MeasureTheory

namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability
open StatMech.OSSS.MonotonicFK


















theorem oqu_fk_q2_sharp {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {n : ℕ} (σ : Fin n ≃ Sym2 V) {f : ConfigSpace (Sym2 V) → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var (fkMass G p 2) f
      ≤ ∑ e, AdaptMConditional.revealAdapt (fkMass G p 2) σ f e
          * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
  
  have hf0' : ∀ ω, (0 : ℝ) ≤ f ω := fun ω => hf0 ω
  have hfC : ∀ ω, |f ω| ≤ 1 := fun ω => by
    rw [abs_le]; exact ⟨by linarith [hf0' ω], hf1 ω⟩
  
  have hpos : ∀ ω, 0 < fkMass G p 2 ω := fun ω => fkMass_pos G hp hp1 (by norm_num) ω
  have hμ1 : ∑ ω, fkMass G p 2 ω = 1 := fkMass_sum_eq_one G hp hp1 (by norm_num)
  have hmono : Monotonic.IsMonotonicMeasure (fkMass G p 2) :=
    fkMass_isMonotonic G hp hp1 (by norm_num)
  
  have hTCL : acp_TailCondLaw (fkMass G p 2) σ f :=
    cmn_tailCondLaw hpos hμ1 hmono σ hf hfC
  
  have hBBB : AdaptCondBBB (fkMass G p 2) σ f :=
    otc_adaptCondBBB_of_tailCondLaw σ hfC hTCL
  
  exact adsD_fk_q2_sharp G hp hp1 σ hf hf0 hf1 hBBB

end AdaptDisintegration

end OSSS

end StatMech
