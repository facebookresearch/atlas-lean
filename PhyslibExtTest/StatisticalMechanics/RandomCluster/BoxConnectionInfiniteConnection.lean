/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BoxConnectionInfiniteConnection

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BoxConnectionInfiniteConnection`

* `boxConnEvent_subset_connected` applied in `ℤ²` at box radius `1`: a box connection from a vertex
  to itself is a connection in `ℤ²`;
* `measureReal_boxConnEvent_le_infiniteTwoPointReal` applied to the Dirac measure at the
  all-closed configuration of `ℤ²`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BoxConnectionInfiniteConnection

open _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice MeasureTheory

-- A box connection between two box vertices of `ℤ²` is a connection in `ℤ²`.
example (x y : boxVerts 2 1) (ω : ConfigSpace (Sym2 (Site 2)))
    (h : ω ∈ boxConnEvent 2 1 x y) : StatMech.Lattice.Connected 2 ω x.1 y.1 :=
  boxConnEvent_subset_connected 2 1 x y h

-- The box two-point bound for the Dirac measure at the all-closed configuration.
example (x y : boxVerts 2 3) :
    ((⟨Measure.dirac (fun _ => false), inferInstance⟩ :
        ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real (boxConnEvent 2 3 x y) ≤
      infiniteTwoPointReal (Measure.dirac (fun _ => false)) x.1 y.1 :=
  measureReal_boxConnEvent_le_infiniteTwoPointReal 2 3 _ x y

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BoxConnectionInfiniteConnection
