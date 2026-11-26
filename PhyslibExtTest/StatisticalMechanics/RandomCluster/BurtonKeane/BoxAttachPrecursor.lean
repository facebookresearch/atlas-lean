/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxAttachPrecursor

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BoxAttachPrecursor`

* `bc98_measurableSet_singleSitePrecursor` at explicit sites of `ℤ²`;
* `bc98_mco_iff_exists_precursor` and `bc98_precursor_of_contact` in conditional form;
* `bc98_bk_from_boxAttach` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxAttachPrecursor

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls

-- The single-site precursor event is measurable.
example : MeasurableSet (bc97_SingleSitePrecursor 2 0 0 0 0 0 0) :=
  bc98_measurableSet_singleSitePrecursor 0 0 0 0 0 0

-- Three clusters reaching the origin is the same as some precursor event.
example (ω : ConfigSpace (Sym2 (Site 2))) (h : mco_ThreeClustersReachOrigin ω) :
    ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site 2, ω ∈ bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃ :=
  (bc98_mco_iff_exists_precursor ω).mp h

-- A trifurcation contact gives a precursor event.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (h : tfe_TrifurcationContact ω) :
    ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, ω ∈ bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ :=
  bc98_precursor_of_contact ω h

-- The Burton–Keane conclusion from box attachment data, by type.
example := @bc98_bk_from_boxAttach

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.BoxAttachPrecursor
