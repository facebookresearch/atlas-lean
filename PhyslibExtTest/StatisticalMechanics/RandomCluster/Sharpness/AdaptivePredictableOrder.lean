/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptivePredictableOrder

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.AdaptivePredictableOrder`

All checks use the one-query decision tree on `s(0, 1)` over the edges of the complete graph on
`Fin 2`.

* `decisionTree_realizedEquiv_predictable`: its realized orders are predictable;
* `prefixSet_decisionTree_realizedEquiv_queried`: the first realized coordinate is `s(0, 1)`;
* `stopVal_decisionTree_realizedEquiv_le_queried_card` for the random-cluster mass at `p = 1/2`,
  `q = 2`: the stopping time is at most `1`, conditional on the code hitting `base`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptivePredictableOrder

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.AdaptiveCausalKernel
open _root_.StatMech.OSSS.MonotonicFK _root_.StatMech.OSSS.Coding

-- Decision-tree orders are predictable.
example : AdaptiveCodingLaw.PredictableOrder (fun x =>
    realizedEquiv (extendDecisionTree (.node s(0, 1) (.leaf true) (.leaf false)) x
      (Finset.univ : Finset (Sym2 (Fin 2)))) x) :=
  decisionTree_realizedEquiv_predictable _

-- The one-query tree reveals `s(0, 1)` first.
example (base : ConfigSpace (Sym2 (Fin 2))) :
    prefixSet (realizedEquiv (extendDecisionTree (.node s(0, 1) (.leaf true) (.leaf false)) base
        Finset.univ) base : Fin (Fintype.card (Sym2 (Fin 2))) → Sym2 (Fin 2)) 1 = {s(0, 1)} := by
  have h := prefixSet_decisionTree_realizedEquiv_queried
    (.node s(0, 1) (.leaf true) (.leaf false)) base
  simpa [DecisionTree.queried] using h

-- The stopping time of the one-query tree is at most `1`.
example (base : ConfigSpace (Sym2 (Fin 2))) (U : Fin (Fintype.card (Sym2 (Fin 2))) → ℝ)
    (hU : codeMap (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
      (realizedEquiv (extendDecisionTree (.node s(0, 1) (.leaf true) (.leaf false)) base
        Finset.univ) base : Fin (Fintype.card (Sym2 (Fin 2))) → Sym2 (Fin 2)) U = base) :
    AdaptMConditional.stopVal (fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
      (realizedEquiv (extendDecisionTree (.node s(0, 1) (.leaf true) (.leaf false)) base
        Finset.univ) base)
      (DecisionTree.evalR (.node s(0, 1) (.leaf true) (.leaf false))) U ≤ 1 := by
  have h := stopVal_decisionTree_realizedEquiv_le_queried_card _ _ base U hU
  simpa [DecisionTree.queried] using h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.AdaptivePredictableOrder
