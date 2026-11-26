/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuinePrecursor

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GenuinePrecursor`

* `bc97_genuineCount_le_interior_plus_boundary` on the upper-lines configuration (instance).
* The fourth conjunct of `bc97_status`: boundary classical trifurcations are at most `|∂B_n|`.
* `bc97_precursor_subset_force_genuineTrif` and `bc97_forceOrigin_genuineTrif` as conditional
  statements: a precursor configuration becomes a classical trifurcation after forcing.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuinePrecursor

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- Interior plus boundary decomposition for the upper-lines configuration.
example : bc89_genuineTcount bc60_upperLines 3 ≤
    (bc97_interiorGenuineFinset bc60_upperLines 3).card + boxSV_boundaryCard 2 3 :=
  bc97_genuineCount_le_interior_plus_boundary _ 3

-- Boundary classical trifurcations are bounded by the boundary size.
example (ω : ConfigSpace (Sym2 (Site 2))) :
    (bc97_boundaryGenuineFinset ω 2).card ≤ boxSV_boundaryCard 2 2 :=
  bc97_status.2.2.2.1 ω 2

-- A precursor configuration becomes a classical trifurcation after forcing.
example (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) (ω : ConfigSpace (Sym2 (Site 2)))
    (h : ω ∈ bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃) :
    bc89_GenuineTrif 2 (forceOpenFinset {s((0 : Site 2), a₁), s(0, a₂), s(0, a₃)} ω) 0 :=
  bc97_precursor_subset_force_genuineTrif a₁ a₂ a₃ x₁ x₂ x₃ h

-- The same through `bc97_forceOrigin_genuineTrif`.
example (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2) (ω : ConfigSpace (Sym2 (Site 2)))
    (h : ω ∈ bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃) :
    bc89_GenuineTrif 2 (forceOpenFinset {s((0 : Site 2), a₁), s(0, a₂), s(0, a₃)} ω) 0 :=
  bc97_forceOrigin_genuineTrif ω h.1 h.2.1 h.2.2.1 h.2.2.2

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GenuinePrecursor
