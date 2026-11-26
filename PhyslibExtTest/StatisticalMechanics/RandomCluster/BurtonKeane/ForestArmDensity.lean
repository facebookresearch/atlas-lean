/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestArmDensity

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestArmDensity`

* `bc95_status`: the upper-lines configuration has genuine count `0` and `N = ⊤`;
* `bc95_spanForest_exists` for the complete graph on `Fin 3`;
* `bc95_bk_from_residues` and `bc95_density_of_singleSiteRewiring` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestArmDensity

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- The upper lines have no genuine trifurcation in the radius-3 box, yet `N = ⊤`.
example : bc89_genuineTcount bc60_upperLines 3 = 0 ∧ numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc95_status.{0}.2.2.2.2.2 3

-- The complete graph on three vertices has a spanning forest.
example : ∃ F : SimpleGraph (Fin 3), F ≤ ⊤ ∧ F.IsAcyclic ∧
    (∀ {u v : Fin 3}, (⊤ : SimpleGraph (Fin 3)).Reachable u v → F.Reachable u v) :=
  bc95_spanForest_exists ⊤

-- Probability zero plus single-site rewiring exclude `N = ⊤`.
example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (h0 : μ {ω | bc89_GenuineTrif 2 ω 0} = 0) (hrw : bc95_SingleSiteRewiring μ) :
    μ {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bc95_bk_from_residues μ h0 hrw

-- Single-site rewiring gives genuine trifurcations of positive density.
example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) (hrw : bc95_SingleSiteRewiring μ) :
    bc94_GenuineTrifExistence μ :=
  bc95_density_of_singleSiteRewiring μ hrw

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.ForestArmDensity
