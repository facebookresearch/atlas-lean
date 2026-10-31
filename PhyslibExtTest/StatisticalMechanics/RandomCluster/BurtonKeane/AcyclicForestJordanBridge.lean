/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicForestJordanBridge

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicForestJordanBridge`

* `Bc52Witness.thetaG_not_acyclic`: the theta graph on `Fin 4` has a cycle;
* `bc52_subgraph_acyclic` applied to the spanning forest of the theta graph;
* `bc52_acyclic_no_boundedRegion` and `bc52_globalArmForest_of_canonical` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicForestJordanBridge

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The theta graph is not acyclic.
example : ¬ Bc52Witness.thetaG.IsAcyclic := Bc52Witness.thetaG_not_acyclic

-- Its spanning forest is acyclic.
example : (osf_spanForest Bc52Witness.thetaG).IsAcyclic :=
  bc52_subgraph_acyclic Bc52Witness.thetaG _ le_rfl

-- An acyclic planar subgraph has no bounded face region.
example (P : PlanarZ2Subgraph) (hac : P.G.IsAcyclic) :
    IsEmpty {c : (whb_faceRegion (imageGraph P)).ConnectedComponent // c.supp.Finite} :=
  bc52_acyclic_no_boundedRegion P hac

-- Canonical trifurcations with arms in the box give the global arm forest.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
    (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
    bc51_GlobalArmForest ω n :=
  bc52_globalArmForest_of_canonical ω n hn hcanon harmbox hexists

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.AcyclicForestJordanBridge
