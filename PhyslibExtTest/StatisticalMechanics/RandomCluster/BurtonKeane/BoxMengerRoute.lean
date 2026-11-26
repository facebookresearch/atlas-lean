/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMengerRoute

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMengerRoute`

* `bc55_naive_collapse_false_of_notNeighbour` at the origin (no site is its own neighbour);
* `bc55_originNeighbour_avoiding_cluster` in conditional form;
* `bc55_burton_keane_bernoulli_of_boxMenger` and `bc55_burton_keane_bernoulli_of_routingCover`
  checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMengerRoute

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The origin is not its own neighbour, so the naive collapse fails there.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) :
    ¬ ((hypercubicLattice d).Adj 0 0 ∧ (0 : Site d) ∈ cluster d ω 0) :=
  bc55_naive_collapse_false_of_notNeighbour ω 0 fun _ h => h.ne.symm

-- No origin neighbour in the cluster.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hno : ∀ a : Site d, (hypercubicLattice d).Adj 0 a → a ∉ cluster d ω x) :
    ¬ ∃ a : Site d, (hypercubicLattice d).Adj 0 a ∧ a ∈ cluster d ω x :=
  bc55_originNeighbour_avoiding_cluster ω x hno

-- The Bernoulli Burton–Keane routes, by type.
example := @bc55_burton_keane_bernoulli_of_boxMenger
example := @bc55_burton_keane_bernoulli_of_routingCover

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxMengerRoute
