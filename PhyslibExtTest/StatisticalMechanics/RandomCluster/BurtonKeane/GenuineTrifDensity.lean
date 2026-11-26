/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifDensity

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifDensity`

* The last conjunct of `bc94_status`: the upper-lines configuration has infinitely many infinite
  clusters but no classical trifurcation (instance).
* `bc94_ae_genuineCount_bound_of_residue` for the zero measure, where the residue holds trivially
  (non-vacuity of the conditional).
* `bc94_exclude_top_of_density` as a conditional statement.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifDensity

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls
open MeasureTheory

-- The upper-lines configuration: `N = ∞` but no classical trifurcation in `B_2`.
example : bc89_genuineTcount bc60_upperLines 2 = 0 ∧ numInfiniteClusters 2 bc60_upperLines = ⊤ :=
  bc94_status.2.2.2.2.2 2

/-- The density residue holds for the zero measure. -/
theorem zero_residue : bc94_DensityForestResidue (0 : Measure (ConfigSpace (Sym2 (Site 2)))) :=
  fun _ => by simp

-- The almost-sure counting bound for the zero measure.
example : ∀ᵐ ω ∂(0 : Measure (ConfigSpace (Sym2 (Site 2)))),
    bc89_genuineTcount ω 3 ≤ boxSV_boundaryCard 2 3 :=
  bc94_ae_genuineCount_bound_of_residue _ zero_residue 3

-- Zero classical-trifurcation probability and the existence step exclude `N = ∞`.
example (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (h0 : μ {ω | bc89_GenuineTrif 2 ω 0} = 0) (hex : bc94_GenuineTrifExistence μ) :
    μ {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bc94_exclude_top_of_density μ h0 hex

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuineTrifDensity
