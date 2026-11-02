/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.CrossNestedEndpoint

/-!
# Tests for `Sheffield.CrossNestedEndpoint`

Module under test: `Sheffield.CrossNestedEndpoint` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* Refutation: `EndpointBridgedRectangleArrayCertificate` is empty for every dual pair and
  probability measure (`EndpointBridgedRectangleArrayCertificate.false`, stated as `IsEmpty`).
* Refutation: `CrossNestedOutwardEndpointCertificate` is empty for every FKG, translation-invariant
  measure with a unique infinite cluster and translation-invariant dual image.
* `PeriodicPlanarDualPair.crossNestedOutwardEndpointCertificate_hypothesis_iff` elaborates
  (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace CrossNestedEndpoint

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- Endpoint-bridged rectangle-array certificates do not exist.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] : IsEmpty (D.EndpointBridgedRectangleArrayCertificate mu) :=
  ⟨PeriodicPlanarDualPair.EndpointBridgedRectangleArrayCertificate.false D mu⟩

-- Cross-nested outward endpoint certificates do not exist under the Sheffield hypotheses.
example (D : PeriodicPlanarDualPair P Pdual) (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu] (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
    IsEmpty (D.CrossNestedOutwardEndpointCertificate mu) :=
  ⟨fun data => PeriodicPlanarDualPair.CrossNestedOutwardEndpointCertificate.false D mu data hFKG
    hTI hunique hTIDual⟩

open PeriodicPlanarDualPair in
example := @crossNestedOutwardEndpointCertificate_hypothesis_iff

end CrossNestedEndpoint
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
