/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-! # Identity closure for TopCat weak homotopy equivalences

The sibling providers
`TopCatWeakHomotopyEquivalence` in the same legacy-model directory
(supplying `TopCat.weakHomotopyEquivalences =
SSet.KanComplex.W.inverseImage TopCat.toSSet`) and
`MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic`
(supplying `TopCat.toSSet_obj_kanComplex`) are imported and reused here. The
polymorphic singular-Kan provider remains public; this file adds only
identity closure and defines no fallback.

Identities are weak homotopy equivalences via `SSet.KanComplex.W.id` after
rewriting `TopCat.toSSet.map` of an identity with `TopCat.toSSet.map_id`.
`ContainsIdentities` is proved in every universe. No
`CategoryWithWeakEquivalences` instance, model structure, product theorem,
or KQ4 statement is added.

Mathematical source: Goerss--Jardine, Simplicial Homotopy Theory, I.3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace TopCat

/-- Identities are TopCat weak homotopy equivalences, via an explicit
polymorphic singular-Kan witness and `SSet.KanComplex.W.id`. -/
instance : (weakHomotopyEquivalences.{u} :
    MorphismProperty TopCat.{u}).ContainsIdentities where
  id_mem X := by
    let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
      TopCat.toSSet_obj_kanComplex X
    change SSet.KanComplex.W (TopCat.toSSet.map (𝟙 X))
    rw [TopCat.toSSet.map_id]
    exact SSet.KanComplex.W.id

end TopCat
