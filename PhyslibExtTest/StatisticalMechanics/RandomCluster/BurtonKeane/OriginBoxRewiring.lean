/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginBoxRewiring

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginBoxRewiring`

* `bc9_originRewiring_of_boxOriginReach` and `bc9_canonicalTrif_of_boxOriginReach` as conditional
  statements in `ℤ²`: box origin reach gives origin rewiring, and on `threeMeetBox` a forced
  pattern away from the origin with a canonical trifurcation there.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginBoxRewiring

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

-- Box origin reach gives origin rewiring.
example (n : ℕ) (h : bc9_BoxOriginReach 2 n) : bc8_OriginRewiring 2 n :=
  bc9_originRewiring_of_boxOriginReach n h

-- ... and a canonical trifurcation at the origin after forcing edges away from it.
example (n : ℕ) (h : bc9_BoxOriginReach 2 n) (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ threeMeetBox 2 n) :
    ∃ W : Finset (Sym2 (Site 2)), (∀ e ∈ W, (0 : Site 2) ∉ e) ∧
      IsCanonicalTrifurcation 2 (forceOpenFinset W ω) 0 :=
  bc9_canonicalTrif_of_boxOriginReach n h ω hω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.OriginBoxRewiring
