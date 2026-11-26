/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutStarTransport

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CutStarTransport`

On the explicit star `bfct_star` (centre `0`, leaves `1, 2, 3`) and its restriction to
`bfct_starS = {0, 1, 2}`:
* `bfct_star_cut`: deleting the centre separates `1` and `2`;
* `bfct_cut_transport` carries this cut to the restriction (`bfct_transport_witness`);
* `bfct_restrict_adj` at an explicit pair.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutStarTransport

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

-- Deleting the centre of the star separates two leaves.
example : ¬ (bkg_deleteVertex bfct_star (0 : Fin 4)).Reachable 1 2 :=
  bfct_star_cut

-- The cut transports to the restriction.
example : ¬ (bkg_deleteVertex (bfct_restrict bfct_star bfct_starS)
    (⟨0, by decide⟩ : {v // v ∈ bfct_starS})).Reachable
    (⟨1, by decide⟩ : {v // v ∈ bfct_starS}) (⟨2, by decide⟩ : {v // v ∈ bfct_starS}) :=
  bfct_cut_transport bfct_star_cut

-- The same, as recorded by the library.
example : ¬ (bkg_deleteVertex (bfct_restrict bfct_star bfct_starS)
    (⟨0, by decide⟩ : {v // v ∈ bfct_starS})).Reachable
    (⟨1, by decide⟩ : {v // v ∈ bfct_starS}) (⟨2, by decide⟩ : {v // v ∈ bfct_starS}) :=
  bfct_transport_witness

-- Restricted adjacency is ambient adjacency.
example : (bfct_restrict bfct_star bfct_starS).Adj ⟨0, by decide⟩ ⟨1, by decide⟩ ↔
    bfct_star.Adj 0 1 :=
  bfct_restrict_adj _ _ _ _


/-! ## Diagnostics moved from the production module -/

-- The `#check` / `#print axioms` commands below were moved here from
-- `StatisticalMechanics/RandomCluster/BurtonKeane/CutStarTransport.lean`: diagnostics belong in tests, not in production modules.
#check @bfct_restrict
#check @bfct_cut_transport
#check @bfct_count
#check @bfct_transport_witness
#check @bfct_status
#print axioms StatMech.Walls.bfct_restrict
#print axioms StatMech.Walls.bfct_cut_transport
#print axioms StatMech.Walls.bfct_count
#print axioms StatMech.Walls.bfct_hub_cut_of_separation
#print axioms StatMech.Walls.bfct_origin_feed
#print axioms StatMech.Walls.bfct_transport_witness
#print axioms StatMech.Walls.bfct_status

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CutStarTransport
