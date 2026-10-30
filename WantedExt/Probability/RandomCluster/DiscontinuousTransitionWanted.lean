/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import PhyslibExt.StatisticalMechanics.RandomCluster.OrderTransition

/-!
# Discontinuity of the planar random-cluster phase transition for `q > 4`

For `q > 4` the random-cluster model on `ℤ²` has a first-order phase transition at the self-dual
point `p_sd(q) = √q / (1 + √q)`: the free measure does not percolate (its connection
probabilities decay exponentially) while the wired measure percolates.

The ported library defines the property (`StatMech.FK.IsFirstOrderTransition`) and derives its
consequences, but takes `θ⁰(p_sd, q) = 0` and `θ¹(p_sd, q) > 0` as hypotheses
(`StatMech.FK.order_transition_q_large_selfDual`, hypotheses `hFree`, `hWired`). A proof of
`first_order_transition_q_gt_four` discharges both.

For `q ≥ 1` the free and wired box measures converge, so `StatMech.FK.freeInfiniteVolume` and
`StatMech.FK.wiredInfiniteVolume` (subsequential limits chosen by Prokhorov compactness) are the
standard measures `φ⁰_{p,q}` and `φ¹_{p,q}`.

## Main statements

* `first_order_transition_q_gt_four`: `θ⁰(p_sd, q) = 0 < θ¹(p_sd, q)` for every `q > 4`.

## References

* H. Duminil-Copin, M. Gagnebin, M. Harel, I. Manolescu, V. Tassion, *Discontinuity of the phase
  transition for the planar random-cluster and Potts models with q > 4*, Ann. Sci. Éc. Norm.
  Supér. (4) 54 (2021), 1363–1413.
-/

@[expose] public section

namespace MathlibExt.Probability.RandomCluster.DiscontinuousTransitionWanted

open StatMech StatMech.FK StatMech.BeffaraDC

/-- **Discontinuity of the phase transition for `q > 4`** (Duminil-Copin, Gagnebin, Harel,
Manolescu, Tassion). For every `q > 4`, at the self-dual point `p_sd(q) = √q / (1 + √q)` the free
random-cluster measure on `ℤ²` does not percolate and the wired one does:
`θ⁰(p_sd, q) = 0 < θ¹(p_sd, q)`.

Source: H. Duminil-Copin, M. Gagnebin, M. Harel, I. Manolescu, V. Tassion, *Discontinuity of the
phase transition for the planar random-cluster and Potts models with q > 4*, Ann. Sci. Éc. Norm.
Supér. 54 (2021). -/
public theorem_wanted first_order_transition_q_gt_four :
    ∀ (q : ℝ) (hq : 4 < q),
      IsFirstOrderTransition 2 (selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).1
        (selfDualPoint_mem_Ioo (by linarith : (0 : ℝ) < q)).2 (by linarith : (0 : ℝ) < q)

end MathlibExt.Probability.RandomCluster.DiscontinuousTransitionWanted
