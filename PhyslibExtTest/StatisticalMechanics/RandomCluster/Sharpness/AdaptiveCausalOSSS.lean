/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalOSSS

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalOSSS`

All checks use the random-cluster mass on the complete graph on `Fin 2` at `p = 1/2`, `q = 2`.

* the one-query decision tree on `s(0, 1)` computes a monotone function (hypothesis witness);
* `adaptive_tree_osss` for the one-query tree on `s(0, 1)`;
* `adaptive_tree_osss` for a constant leaf tree;
* `causalTripleJump_le_cov_sharedStep` for the one-query tree at step `0`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalOSSS

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCausalKernel
open _root_.StatMech.OSSS.MonotonicFK

/-- The random-cluster mass on `K₂` at `p = 1/2`, `q = 2`. -/
local notation "μ₂" => fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2

/-- Positivity of `μ₂`. -/
theorem mu2_pos (ω : ConfigSpace (Sym2 (Fin 2))) : 0 < μ₂ ω :=
  fkMass_pos ⊤ (by norm_num) (by norm_num) (by norm_num) ω

/-- `μ₂` is a probability mass. -/
theorem mu2_sum : ∑ ω, μ₂ ω = 1 :=
  fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)

/-- `μ₂` is a monotonic measure. -/
theorem mu2_mono : Monotonic.IsMonotonicMeasure μ₂ :=
  fkMass_isMonotonic ⊤ (by norm_num) (by norm_num) (by norm_num)

/-- The decision tree querying `s(0, 1)` and returning its state computes a monotone function. -/
theorem queryEdge_evalR_monotone :
    Monotone (DecisionTree.evalR
      (.node s(0, 1) (.leaf true) (.leaf false) : DecisionTree (Sym2 (Fin 2)))) := by
  intro ω ω' h
  have h01 := h s(0, 1)
  by_cases hω : ω s(0, 1) <;> by_cases hω' : ω' s(0, 1) <;>
    simp_all [DecisionTree.evalR, DecisionTree.eval, Bool.le_iff_imp]

-- Decision-tree OSSS for the one-query tree on `K₂`.
example :
    Lindeberg.var μ₂
        (DecisionTree.evalR (.node s(0, 1) (.leaf true) (.leaf false))) ≤
      ∑ e, LindebergTree.revealmentMu μ₂
          (.node s(0, 1) (.leaf true) (.leaf false)) e *
        Lindeberg.cov μ₂
          (DecisionTree.evalR (.node s(0, 1) (.leaf true) (.leaf false))) (Lindeberg.coord e) :=
  adaptive_tree_osss _ mu2_pos
    mu2_sum
    mu2_mono _ queryEdge_evalR_monotone

-- Decision-tree OSSS for a constant leaf tree.
example :=
  adaptive_tree_osss μ₂ mu2_pos
    mu2_sum
    mu2_mono (.leaf true) (fun _ _ _ => le_rfl)

-- The triple jump of the one-query tree at step `0` is bounded by covariances.
example (seed : ConfigSpace (Sym2 (Fin 2))) :=
  causalTripleJump_le_cov_sharedStep μ₂ mu2_pos
    mu2_sum
    mu2_mono _ queryEdge_evalR_monotone seed 0

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalOSSS
