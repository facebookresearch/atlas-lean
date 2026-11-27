/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalSplice

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalSplice`

* `causalMixLabels_extendDecisionTreeAt_eq_adaptWt` for the one-query decision tree on `s(0, 1)`
  over the edges of the complete graph on `Fin 2`, with the stopping time evaluated to `1`;
* the same identity for a constant leaf tree, where the stopping time is `0`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalSplice

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCausalKernel

-- The one-query tree stops after one step, so the causal labels are `adaptWt U V 1 t`.
example (t : ℕ) (base : ConfigSpace (Sym2 (Fin 2)))
    (U V : Fin (Fintype.card (Sym2 (Fin 2))) → ℝ) :
    causalMixLabels (extendDecisionTreeAt t (.node s(0, 1) (.leaf true) (.leaf false)) base
        Finset.univ) base U V = AdaptMConditional.adaptWt U V 1 t := by
  rw [causalMixLabels_extendDecisionTreeAt_eq_adaptWt]
  simp [DecisionTree.queried]

-- A leaf queries nothing, so the causal labels are `adaptWt U V 0 t`.
example (t : ℕ) (b : Bool) (base : ConfigSpace (Sym2 (Fin 2)))
    (U V : Fin (Fintype.card (Sym2 (Fin 2))) → ℝ) :
    causalMixLabels (extendDecisionTreeAt t (.leaf b) base Finset.univ) base U V =
      AdaptMConditional.adaptWt U V 0 t :=
  causalMixLabels_extendDecisionTreeAt_eq_adaptWt t (.leaf b) base U V

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptiveCausalSplice
