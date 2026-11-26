/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptDisintegration
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptCondReduction
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.CrossMonotone

/-!
# OSSS for the q = 2 random-cluster model

The OSSS inequality for monotone observables of the `q = 2` random-cluster measure on a finite
graph, for any fixed revealment order.

## i. Overview

Assembles the chain for `μ = fkMass G p 2`: the tail conditional law (`CrossMonotone`) gives
`AdaptCondBBB` (`AdaptCondReduction`), hence `AdaptStepCovBound` (`AdaptDisintegration`), hence OSSS
(`AdaptMConditional`). `oqu_fk_q2_sharp` is unconditional.

## ii. Key results

- `oqu_fk_q2_sharp`: `Var f ≤ ∑ revealAdapt(e) · Cov(f, ω_e)` for monotone `0 ≤ f ≤ 1`
  (unconditional).

## iii. Table of contents

- A. The q = 2 OSSS theorem

## iv. References

* R. O'Donnell, M. Saks, O. Schramm, R. Servedio, *Every decision tree has an influential variable*,
  FOCS 2005.
* H. Duminil-Copin, A. Raoufi, V. Tassion, *Sharp phase transition for the random-cluster and Potts
  models via decision trees*, Ann. of Math. 189 (2019).
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability
open StatMech.OSSS.MonotonicFK

/-! ## A. The q = 2 OSSS theorem -/

/-- `Var f ≤ ∑ revealAdapt(e) · Cov(f, ω_e)` for monotone `0 ≤ f ≤ 1` (unconditional). -/
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
