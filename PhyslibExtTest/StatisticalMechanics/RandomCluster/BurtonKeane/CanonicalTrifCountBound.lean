/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCountBound

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCountBound`

* `ccf_canonTcount_le_boundary_of_armForestReaching` and
  `ccf_canonTcount_le_boundary_of_boxOpenForest` in conditional form;
* `ccf_canon_arm_data` checked by type.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCountBound

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Arm forest reaching bounds the canonical count.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : sfa_ArmForestReaching ω n) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  ccf_canonTcount_le_boundary_of_armForestReaching ω n h

-- A box open forest bounds the canonical count.
example {d : ℕ} (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (h : bst_BoxOpenForest ω n) :
    ctc2_canonTcount d ω n ≤ boxSV_boundaryCard d n :=
  ccf_canonTcount_le_boundary_of_boxOpenForest ω n h

-- Arm data of canonical trifurcations, by type.
example := @ccf_canon_arm_data

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonicalTrifCountBound
