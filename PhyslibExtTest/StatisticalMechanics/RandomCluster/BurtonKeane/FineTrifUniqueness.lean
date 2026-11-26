/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrifUniqueness

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrifUniqueness`

In the plane:
* `bfx_coarseSet_eq_fineSet`: scale-zero coarse trifurcations at the origin are fine ones;
* `bfx_deleteVertex_le` for the all-open configuration;
* `bfx_fineTrif_of_classical` and `bfx_bk_atLeastTwo_of_route` (Bernoulli(1/2)) in conditional
  form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrifUniqueness

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation _root_.StatMech.Walls MeasureTheory
open scoped NNReal

/-- The all-open configuration of the planar lattice. -/
def open2 : ConfigSpace (Sym2 (Site 2)) := fun _ => true

-- Coarse and fine trifurcation events at scale zero coincide.
example : {ω : ConfigSpace (Sym2 (Site 2)) | bc61_IsCoarseTrifurcation ω 0 0}
    = {ω | bft_FineTrif ω 0} :=
  bfx_coarseSet_eq_fineSet

-- Deleting the origin is below removing it.
example : bkg_deleteVertex (openSubgraph 2 open2) 0 ≤ openSubgraph 2 (removeSite 0 open2) :=
  bfx_deleteVertex_le open2

-- Classical trifurcations at the origin are fine.
example (ω : ConfigSpace (Sym2 (Site 2))) (h : bc47_IsClassicalTrifurcation ω 0) :
    bft_FineTrif ω 0 :=
  bfx_fineTrif_of_classical ω h

-- The route hypothesis excludes two infinite clusters for Bernoulli(1/2).
example (hroute : ∀ n : ℕ,
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num) (threeMeetBox 2 n) →
      ∃ a₁ a₂ a₃ : Site 2, 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2)
        (by norm_num) (NeighborTrifPrecursor 2 a₁ a₂ a₃)) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) (1 / 2) (by norm_num) (atLeastTwoInfinite 2)
      = 0 :=
  bfx_bk_atLeastTwo_of_route (by norm_num) _ _ (by norm_num) hroute

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.FineTrifUniqueness
