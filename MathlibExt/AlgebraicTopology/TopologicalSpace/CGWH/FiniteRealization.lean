/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.CompactlyGenerated.FiniteRealization
public import MathlibExt.Topology.Category.CGWH.Basic

/-!
# Finite simplicial realizations in CGWH

The compact-generation and weak-Hausdorff point-set facts are supplied by
the neutral compactly-generated provider. This file only bundles the literal
finite realization carrier and topology as a CGWH space.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

namespace SSet

/-- A finite simplicial realization as a CGWH space, with the literal
realization carrier and topology. -/
noncomputable def toCGWHOfFinite
    (K : SSet.{v}) [K.Finite] : CGWH.{u, v} where
  toCompactlyGenerated := toCompactlyGeneratedOfFinite K
  is_weakHausdorff := uWeakHausdorffSpace_realization_of_finite K

end SSet
