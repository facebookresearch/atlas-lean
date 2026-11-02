/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalOriginRewiring

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalOriginRewiring`

* `bc8_arm_ne_of_cut_ne` and `bc8_isCanonicalTrifurcation_of_originSplits` in conditional form;
* `bc8_threeArmsNoCrossing_isCanonical` at `n = 2` in `ℤ²`;
* `bc8_burtonKeane_uniqueness_of_originRewiring` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalOriginRewiring

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation
open _root_.StatMech.Walls

-- Distinct cut clusters have distinct roots.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) {a b : Site d}
    (h : cluster d (removeSite 0 ω) a ≠ cluster d (removeSite 0 ω) b) : a ≠ b :=
  bc8_arm_ne_of_cut_ne h

-- Three origin arms splitting after removing the origin give a canonical trifurcation.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d)))
    (h : ∃ a₁ a₂ a₃ : Site d, (openSubgraph d ω).Adj 0 a₁ ∧ (openSubgraph d ω).Adj 0 a₂ ∧
      (openSubgraph d ω).Adj 0 a₃ ∧ (cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :=
  bc8_isCanonicalTrifurcation_of_originSplits ω h

-- Configurations in the three-meet box, at `n = 2`.
example (ω : ConfigSpace (Sym2 (Site 2))) (hω : ω ∈ threeMeetBox 2 2) :=
  bc8_threeArmsNoCrossing_isCanonical 2 ω hω

-- The origin-rewiring uniqueness theorem, by type.
example := @bc8_burtonKeane_uniqueness_of_originRewiring

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalOriginRewiring
