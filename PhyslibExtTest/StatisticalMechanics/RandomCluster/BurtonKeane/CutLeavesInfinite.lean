/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutLeavesInfinite

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutLeavesInfinite`

In the plane:
* `bc8_cutLeavesInfinite_origin` shows the origin's cluster in the all-closed configuration is
  finite (it would need an open neighbour of the origin);
* `bc8_cutLeavesInfinite` and `bc8_cutLeavesInfinite_inCluster` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutLeavesInfinite

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-closed configuration of the planar lattice. -/
def closed2 : ConfigSpace (Sym2 (Site 2)) := fun _ => false

-- The cluster of the origin in the all-closed configuration is finite.
example : ¬ (cluster 2 closed2 0).Infinite := fun h => by
  obtain ⟨n, hn, -⟩ := bc8_cutLeavesInfinite_origin closed2 h
  exact absurd hn.2 (by simp [closed2])

-- An infinite cluster through the origin leaves an infinite cut cluster at a neighbour.
example (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2) (hinf : (cluster 2 ω x).Infinite)
    (h0 : (0 : Site 2) ∈ cluster 2 ω x) :
    ∃ n, (openSubgraph 2 ω).Adj 0 n ∧ (cluster 2 (removeSite 0 ω) n).Infinite :=
  bc8_cutLeavesInfinite ω hinf h0

-- The neighbour can be taken in the same cluster.
example (ω : ConfigSpace (Sym2 (Site 2))) (x : Site 2) (hinf : (cluster 2 ω x).Infinite)
    (h0 : (0 : Site 2) ∈ cluster 2 ω x) :
    ∃ n, (openSubgraph 2 ω).Adj 0 n ∧ n ∈ cluster 2 ω x ∧
      (cluster 2 (removeSite 0 ω) n).Infinite :=
  bc8_cutLeavesInfinite_inCluster ω hinf h0

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutLeavesInfinite
