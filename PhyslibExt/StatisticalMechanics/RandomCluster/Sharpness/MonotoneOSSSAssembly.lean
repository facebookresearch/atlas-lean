/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.FKQ2SharpTheorem

/-!
# The OSSS inequality for monotonic measures

For a positive monotonic probability measure on `{0, 1}^E`, any revealment order and a monotone `0 ≤
f ≤ 1`, `Var f ≤ ∑ revealAdapt(e) · Cov(f, ω_e)`.

## i. Overview

Assembles the chain: `cmn_tailCondLaw` gives the tail conditional law,
`otc_adaptCondBBB_of_tailCondLaw` gives `AdaptCondBBB`, and `adsD_adaptStepCovBound_of_condBBB`
gives the step bound (`osss_onestep_cov_bound`). Then `tree_osss_sharp_unconditional` gives the
inequality. `osss_monotone_sharp` is unconditional.

## ii. Key results

- `osss_monotone_sharp`: OSSS for monotonic measures (unconditional).

## iii. Table of contents

- A. Assembly

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

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## A. Assembly -/

lemma osss_onestep_cov_bound {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    AdaptStepCovBound μ σ f := by
  have hf0' : ∀ ω, (0 : ℝ) ≤ f ω := fun ω => hf0 ω
  have hfC : ∀ ω, |f ω| ≤ 1 := fun ω => by
    rw [abs_le]; exact ⟨by linarith [hf0' ω], hf1 ω⟩
  have hTCL : acp_TailCondLaw μ σ f := cmn_tailCondLaw hpos hμ1 hmono σ hf hfC
  have hBBB : AdaptCondBBB μ σ f := otc_adaptCondBBB_of_tailCondLaw σ hfC hTCL
  exact adsD_adaptStepCovBound_of_condBBB hpos hmono σ hf hfC hBBB

/-- OSSS for monotonic measures (unconditional). -/
theorem osss_monotone_sharp {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f
      ≤ ∑ e, revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e) :=
  tree_osss_sharp_unconditional hpos hμ1 σ hf0 hf1
    (osss_onestep_cov_bound hpos hμ1 hmono σ hf hf0 hf1)

section FK

variable {V : Type*} [Fintype V] [DecidableEq V]

end FK

end AdaptDisintegration

end OSSS

end StatMech
