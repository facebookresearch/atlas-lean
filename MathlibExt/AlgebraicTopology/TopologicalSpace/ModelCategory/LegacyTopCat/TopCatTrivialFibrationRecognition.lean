/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.BoundaryRLPSingularRLPReflection
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence

/-!
# Topological fibration recognition from simplicial lifting

Assume on `SSet.{u}` that `J.rlp ⊓ KanComplex.W ≤ I.rlp`, for the horn and boundary generator
classes `J` and `I`. The realization–singular adjunction then shows that a map in
`TopCat.realizedHornInclusions.{u}.rlp` which is a weak homotopy equivalence also lies in
`TopCat.realizedBoundaryInclusions.{u}.rlp`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- Assume `SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤ SSet.modelCategoryQuillen.I.{u}.rlp`. Then
`TopCat.realizedHornInclusions.{u}.rlp ⊓ TopCat.weakHomotopyEquivalences ≤ TopCat.realizedBoundaryInclusions.{u}.rlp`.
A topological map with realized-horn right lifting and weak homotopy equivalence therefore has realized-boundary right
lifting. -/
theorem hornRLP_inf_W_le_boundaryRLP_of_sSet
    (hSSet : SSet.modelCategoryQuillen.J.{u}.rlp ⊓ SSet.KanComplex.W.{u} ≤
      SSet.modelCategoryQuillen.I.{u}.rlp) :
    realizedHornInclusions.{u}.rlp ⊓ weakHomotopyEquivalences ≤
      realizedBoundaryInclusions.{u}.rlp := by
  intro X Y f hf
  obtain ⟨hfR, hfW⟩ := hf
  have hSingR : SSet.modelCategoryQuillen.J.{u}.rlp (toSSet.map f) :=
    hornRLP_eq_inverseImage_J_rlp.le _ hfR
  have hSingW : SSet.KanComplex.W.{u} (toSSet.map f) :=
    (mem_weakHomotopyEquivalences_iff f).mp hfW
  have hSingI : SSet.modelCategoryQuillen.I.{u}.rlp (toSSet.map f) :=
    hSSet _ ⟨hSingR, hSingW⟩
  exact inverseImage_I_rlp_le_boundaryRLP _ hSingI

end TopCat
