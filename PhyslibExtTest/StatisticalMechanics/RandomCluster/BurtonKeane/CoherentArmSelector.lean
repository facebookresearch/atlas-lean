/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoherentArmSelector

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoherentArmSelector`

* refutation: `pap_not_forall_coherentSelector` in the plane;
* `pap_far_of_avoiding_path` on the trivial walk at a site away from the removed origin;
* `pap_adj_removeSite_of_avoid` in its conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoherentArmSelector

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Private arms do not exist for every configuration and box in the plane.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 2))) (n : ℕ), 1 ≤ n → daepf_PrivateArm ω n :=
  pap_not_forall_coherentSelector (by norm_num)

-- A site other than the origin stays connected to itself after removing the origin.
example (ω : ConfigSpace (Sym2 (Site 2))) :
    Connected 2 (removeSite 0 ω) (![1, 0] : Site 2) ![1, 0] :=
  pap_far_of_avoiding_path ω (x := 0) SimpleGraph.Walk.nil (by
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
    intro h; simpa using congrFun h 0)

-- Open edges avoiding the removed site stay open.
example (ω : ConfigSpace (Sym2 (Site 2))) (u w : Site 2) (hu : u ≠ 0) (hw : w ≠ 0)
    (hadj : (openSubgraph 2 ω).Adj u w) : (openSubgraph 2 (removeSite 0 ω)).Adj u w :=
  pap_adj_removeSite_of_avoid ω hu hw hadj

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CoherentArmSelector
