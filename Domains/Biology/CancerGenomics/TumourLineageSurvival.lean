/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BranchingProcess.Binary

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Survival probability of a tumour lineage in a discrete-time branching process

Reiter, Bozic, Allen, Chatterjee and Nowak (2013), following Bozic et al. (2010), model tumour
growth as a discrete-time Galton–Watson process started from a single cell: at each time step
every cell independently either divides into two daughters, with probability `(1 + a) / 2`, or
dies, with probability `(1 - a) / 2`. The growth coefficient `a` is the division probability minus
the death probability per step. The offspring law of a cell is therefore
`GaltonWatson.binaryOffspring ((1 + a) / 2)`, with mass `(1 - a) / 2` at `0` and `(1 + a) / 2`
at `2`, and the probability that the lineage goes extinct is its `GaltonWatson.extinctionProb`.

## Main result

* `tumourLineage_survival`: for a growth coefficient `0 < a < 1` the lineage of a single cell goes
  extinct with probability `(1 - a) / (1 + a)` and survives forever with probability
  `P_surv(a) = 2 a / (1 + a)`; moreover `P_surv(a) / a → 2` as `a → 0⁺`, the precise form of
  `P_surv(a) ≈ 2 a` for small `a`.

## Conventions

Time is measured in cell divisions (one step of the process). The survival probability is
`1 - q`, where `q` is the extinction probability of the lineage of one cell. The small-`a` claim
is an exact `Tendsto` statement; no remainder term is claimed. The source's further observation
that one additional driver mutation, acquired at a small rate `u` upon division, leaves the
tumour's survival probability essentially unchanged is a heuristic about timescales and is not
stated here.

## References

* J. G. Reiter, I. Bozic, B. Allen, K. Chatterjee, M. A. Nowak, *The effect of one additional
  driver mutation on tumor progression*, Evolutionary Applications 6 (2013), 34–45
  (Materials and methods, "The model"; Results, first paragraph).
* I. Bozic, T. Antal, H. Ohtsuki, H. Carter, D. Kim, S. Chen, R. Karchin, K. W. Kinzler,
  B. Vogelstein, M. A. Nowak, *Accumulation of driver and passenger mutations during tumor
  progression*, Proc. Natl. Acad. Sci. USA 107 (2010), 18545–18550.
-/

@[expose] public section

open Filter Topology MathlibExt.Probability.GaltonWatson

namespace Domains.Biology.CancerGenomics.TumourLineageSurvival

/-- **Survival probability of a tumour lineage** (Reiter et al. 2013, following Bozic et al.
2010). Let each tumour cell, at each time step, independently divide into two daughters with
probability `(1 + a) / 2` or die with probability `(1 - a) / 2`, so that its offspring law is
`binaryOffspring ((1 + a) / 2)` and the growth coefficient `a` is the division probability minus
the death probability. For every `0 < a < 1`, the lineage of a single cell goes extinct with
probability `(1 - a) / (1 + a)` and survives forever with probability
`P_surv(a) = 1 - (1 - a) / (1 + a) = 2 a / (1 + a)`. Moreover `P_surv(a) / a → 2` as `a → 0⁺`,
which is the statement `P_surv(a) ≈ 2 a` for `a ≪ 1`. -/
theorem tumourLineage_survival :
    (∀ a : ℝ, 0 < a → a < 1 →
      extinctionProb (binaryOffspring ((1 + a) / 2)) = (1 - a) / (1 + a) ∧
        1 - extinctionProb (binaryOffspring ((1 + a) / 2)) = 2 * a / (1 + a)) ∧
      Tendsto (fun a : ℝ => (1 - extinctionProb (binaryOffspring ((1 + a) / 2))) / a)
        (𝓝[>] 0) (𝓝 2) := by
  have hclosed : ∀ a : ℝ, 0 < a → a < 1 →
      extinctionProb (binaryOffspring ((1 + a) / 2)) = (1 - a) / (1 + a) ∧
        1 - extinctionProb (binaryOffspring ((1 + a) / 2)) = 2 * a / (1 + a) := by
    intro a ha0 ha1
    have hq : extinctionProb (binaryOffspring ((1 + a) / 2)) = (1 - a) / (1 + a) := by
      rw [extinctionProb_binaryOffspring_of_gt (by linarith) (by linarith) (by linarith)]
      have h1a : (1 + a) ≠ 0 := by linarith
      field_simp
      ring
    refine ⟨hq, ?_⟩
    rw [hq]
    have h1a : (1 + a) ≠ 0 := by linarith
    field_simp
    ring
  refine ⟨hclosed, ?_⟩
  have hcont : ContinuousAt (fun a : ℝ => 2 / (1 + a)) 0 :=
    continuousAt_const.div (continuousAt_const.add continuousAt_id) (by norm_num)
  have hlim : Tendsto (fun a : ℝ => 2 / (1 + a)) (𝓝[>] 0) (𝓝 2) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with a ha
  rw [(hclosed a ha.1 ha.2).2]
  have ha0 : a ≠ 0 := ha.1.ne'
  have h1a : (1 + a) ≠ 0 := by linarith [ha.1]
  field_simp

end Domains.Biology.CancerGenomics.TumourLineageSurvival
