/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.PairedRecurrence

/-!
# Tests for `Sheffield.PairedRecurrence`

Module under test: `Sheffield.PairedRecurrence` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* Refutations (any dual pair and probability measure, stated as `IsEmpty`):
  `PointwiseRecursiveRectangleArrayCertificate` and `ComplementaryCrossNestedLimitCertificate`.
* `PeriodicPlanarDualPair.PaddedPairedAdjacentTransition.false` and
  `PeriodicPlanarDualPair.carriedCrossNestedArrays_false` elaborate (check-only; their
  hypotheses need schedule data with no cheap instance).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace PairedRecurrence

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- Pointwise recursive rectangle-array certificates do not exist.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] : IsEmpty (D.PointwiseRecursiveRectangleArrayCertificate mu) :=
  ⟨PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.false D mu⟩

-- Complementary cross-nested limit certificates do not exist.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] : IsEmpty (D.ComplementaryCrossNestedLimitCertificate mu) :=
  ⟨PeriodicPlanarDualPair.ComplementaryCrossNestedLimitCertificate.false D mu⟩

-- `PeriodicPlanarDualPair.PaddedPairedAdjacentTransition.false` elaborates.
example := @PeriodicPlanarDualPair.PaddedPairedAdjacentTransition.false

-- `PeriodicPlanarDualPair.carriedCrossNestedArrays_false` elaborates.
example := @PeriodicPlanarDualPair.carriedCrossNestedArrays_false

end PairedRecurrence
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
