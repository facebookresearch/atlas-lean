/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.BoundaryRLPSingularRLP
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic
import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Conditional boundary-RLP weak-equivalence bridge

This file is part of the KQ3 layer. It composes the staged KQ3
adjunction-transport provider `TopCat.boundaryRLP_le_inverseImage_I_rlp`
with an explicit Kan-restricted KQ2 hypothesis
`∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f` to obtain
`TopCat.realizedBoundaryInclusions.rlp ≤ TopCat.weakHomotopyEquivalences`.

The unrestricted premise `SSet.modelCategoryQuillen.I.rlp ≤ SSet.KanComplex.W`
is false: identities on non-Kan simplicial sets lie in `I.rlp`, while
`SSet.KanComplex.W` requires Kan source and target. Hence the hypothesis is
restricted to Kan source and target; singular complexes of spaces are Kan, so
the restricted premise applies to `TopCat.toSSet.map f`.

This proves only the formal transport conditional. It does not supply the
restricted SSet premise, claims no unconditional inclusion, and adds no model
structure.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat

/-- Conditional bridge: the Kan-restricted KQ2 boundary-RLP hypothesis implies realized
boundary-RLP maps are weak homotopy equivalences. The unrestricted `I.rlp ≤ W`
is false by the non-Kan identity counterexample. -/
theorem boundaryRLP_le_weakHomotopyEquivalences_of_kanRestricted_Irlp_le_W
    (h : ∀ {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y] {f : X ⟶ Y},
      SSet.modelCategoryQuillen.I.{u}.rlp f → SSet.KanComplex.W.{u} f) :
    realizedBoundaryInclusions.{u}.rlp ≤ weakHomotopyEquivalences := by
  intro X Y f hf
  let _ : SSet.KanComplex (toSSet.obj X) := toSSet_obj_kanComplex X
  let _ : SSet.KanComplex (toSSet.obj Y) := toSSet_obj_kanComplex Y
  have hI : SSet.modelCategoryQuillen.I.{u}.rlp (toSSet.map f) :=
    boundaryRLP_le_inverseImage_I_rlp _ hf
  have hW : SSet.KanComplex.W.{u} (toSSet.map f) := h hI
  exact (mem_weakHomotopyEquivalences_iff f).mpr hW

end TopCat
