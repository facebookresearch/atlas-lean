/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ConwayKnotEuclideanBridge

namespace ConwayKnotEuclideanBridgeTest

open MathlibExt.Topology.ConwayKnotShared.KnotTheory
open MathlibExt.Topology.ConwayKnotEuclideanBridge
open MathlibExt.Topology.Knot.Euclidean (ParametrizedLink)

-- Conversion preserves the order and parametrizations of the two components.
example (L : TwoLink) :
    ((toParametrizedLink L).component 0).curve = L.K.curve ∧
      ((toParametrizedLink L).component 1).curve = L.L.curve :=
  ⟨rfl, rfl⟩

-- Isotopic benchmark links have the same Euclidean type ropelength.
example {L₁ L₂ : TwoLink} (h : L₁.Isotopic L₂) :
    (toParametrizedLink L₁).ropelength = (toParametrizedLink L₂).ropelength :=
  ParametrizedLink.ropelength_eq_of_isotopic (twoLink_isotopic_iff.mp h)

end ConwayKnotEuclideanBridgeTest
