/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.ActiveEdgeRussoP

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ActiveEdgeRussoP`

On the one-edge graph `⊤` on `Fin 2` at `p = 1/2`, `q = 2`:
* `centeredScore_extendActive` relates the centred score to `activePScore`;
* `hasDerivAt_activeMean_p` for the constant function `1`;
* `hasDerivAt_activeProbOf_p` (Russo's formula in `p`) for the sure event.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ActiveEdgeRussoP

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- The centred edge score of an extension is the active `p`-score.
example (ω : ConfigSpace G2.edgeSet) :
    (∑ e ∈ G2.edgeFinset, (coord e (extendActive G2 ω) - 1 / 2)) = activePScore G2 (1 / 2) ω :=
  centeredScore_extendActive G2 _ ω

-- The `p`-derivative of an active expectation.
example : HasDerivAt (fun x => activeMean G2 (fun _ => x) 2 (fun _ => 1))
    ((∑ e : G2.edgeSet, activeCov G2 (fun _ => 1 / 2) 2 (fun _ => 1)
      (OSSS.Lindeberg.coord e)) / (1 / 2 * (1 - 1 / 2))) (1 / 2) :=
  hasDerivAt_activeMean_p G2 (by norm_num) (by norm_num) (by norm_num) _

-- Russo's formula in `p` for the sure event.
example : HasDerivAt (fun x => activeProbOf G2 (fun _ => x) 2 Set.univ)
    ((∑ e : G2.edgeSet, activeCov G2 (fun _ => 1 / 2) 2
      (Set.univ.indicator fun _ => (1 : ℝ)) (OSSS.Lindeberg.coord e)) /
        (1 / 2 * (1 - 1 / 2))) (1 / 2) :=
  hasDerivAt_activeProbOf_p G2 (by norm_num) (by norm_num) (by norm_num) _

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ActiveEdgeRussoP
