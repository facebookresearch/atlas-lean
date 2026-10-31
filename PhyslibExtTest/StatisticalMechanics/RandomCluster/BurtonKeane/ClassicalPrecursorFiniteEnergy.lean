/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalPrecursorFiniteEnergy

/-!
# Tests for `ClassicalPrecursorFiniteEnergy`

Module under test:
`PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ClassicalPrecursorFiniteEnergy`

* `bc49_precursor_subset_force_classicalTrif` at explicit sites of `ℤ²`;
* `bc49_classicalTrif_pos_of_precursor_pos` in conditional form;
* `bc49_burton_keane_bernoulli_of_routingCover` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane
namespace ClassicalPrecursorFiniteEnergy

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- Forcing the three origin edges turns a precursor into a classical trifurcation.
example := bc49_precursor_subset_force_classicalTrif (d := 2) (Pi.single 0 1) (Pi.single 1 1)
  (Pi.single 0 (-1))

-- A positive-probability precursor gives positive classical-trifurcation probability.
example {d : ℕ} (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site d))))
    [MeasureTheory.IsProbabilityMeasure μ] (hfe : HasFiniteEnergyMerge μ) (a₁ a₂ a₃ : Site d)
    (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
    0 < μ {ω | bc47_IsClassicalTrifurcation ω 0} :=
  bc49_classicalTrif_pos_of_precursor_pos μ hfe a₁ a₂ a₃ hpos

-- The routing-cover Burton–Keane route, by type.
example := @bc49_burton_keane_bernoulli_of_routingCover

end ClassicalPrecursorFiniteEnergy
end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane
