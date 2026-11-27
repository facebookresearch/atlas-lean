/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatWeakHomotopyEquivalence
public import
  MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Identity maps are weak homotopy equivalences

For every universe `u` and space `X : TopCat.{u}`, the identity map of `X` is a weak homotopy
equivalence. The singular simplicial set of `X` is Kan, and its identity belongs to
`SSet.KanComplex.W`.

See Goerss–Jardine, *Simplicial Homotopy Theory*, I.3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace TopCat

/-- For every universe `u`, `TopCat.weakHomotopyEquivalences.{u}` contains identities: `𝟙 X` is a
weak homotopy equivalence for each `X : TopCat.{u}`. Applying the singular functor gives the
identity of a Kan simplicial set, which lies in `SSet.KanComplex.W`. -/
instance : (weakHomotopyEquivalences.{u} :
    MorphismProperty TopCat.{u}).ContainsIdentities where
  id_mem X := by
    let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
      TopCat.toSSet_obj_kanComplex X
    change SSet.KanComplex.W (TopCat.toSSet.map (𝟙 X))
    rw [TopCat.toSSet.map_id]
    exact SSet.KanComplex.W.id

end TopCat
