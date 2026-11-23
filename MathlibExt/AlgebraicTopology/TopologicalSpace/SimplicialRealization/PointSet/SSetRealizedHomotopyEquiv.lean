/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Realized simplicial homotopy equivalence

For `X Y : SSet.{u}`, `f : X ⟶ Y`, `g : Y ⟶ X`, with simplicial homotopies
`Hleft : SSet.Homotopy (f ≫ g) (𝟙 X)` and `Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)`,
the realizations are homotopy equivalent via realized `f` forward and realized
`g` backward, using `SSet.realizeHomotopy` on each side with functor
`map_comp`/`map_id` rewrites.

Orientation (do not flip): `Hleft` runs from the composite `f ≫ g` to the
identity on `X`, so its realization runs from realized `f` then realized `g`
to the identity on `|X|`; `Hright` is the symmetric statement on `Y`.
The construction is universe-polymorphic in `X Y : SSet.{u}` through
`SSet.realizeHomotopyMap` and `SSet.realizeHomotopy`.

The construction realizes the two homotopy inverse laws on simplicial sets
through the original geometric-realization functor.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SSet

/-- Homotopy equivalence between realizations from mutually inverse simplicial
maps up to simplicial homotopy. -/
noncomputable def realizedHomotopyEquiv (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ContinuousMap.HomotopyEquiv (SSet.toTop.obj X) (SSet.toTop.obj Y) where
  toFun := (SSet.toTop.map f).hom
  invFun := (SSet.toTop.map g).hom
  left_inv := by
    have hL := SSet.realizeHomotopy X X (f ≫ g) (𝟙 X) Hleft
    have hL' : ContinuousMap.Homotopy
        ((SSet.toTop.map g).hom.comp (SSet.toTop.map f).hom)
        (ContinuousMap.id _) := by
      simpa [Functor.map_comp, TopCat.hom_comp, Functor.map_id, TopCat.hom_id] using hL
    exact ⟨hL'⟩
  right_inv := by
    have hR := SSet.realizeHomotopy Y Y (g ≫ f) (𝟙 Y) Hright
    have hR' : ContinuousMap.Homotopy
        ((SSet.toTop.map f).hom.comp (SSet.toTop.map g).hom)
        (ContinuousMap.id _) := by
      simpa [Functor.map_comp, TopCat.hom_comp, Functor.map_id, TopCat.hom_id] using hR
    exact ⟨hR'⟩

/-- Coercion of `SSet.realizedHomotopyEquiv` is the forward realized map. -/
@[simp]
theorem coe_realizedHomotopyEquiv (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ⇑(realizedHomotopyEquiv X Y f g Hleft Hright) = ⇑(SSet.toTop.map f).hom :=
  rfl

/-- Coercion of the symmetric `SSet.realizedHomotopyEquiv` is the backward realized map. -/
@[simp]
theorem coe_symm_realizedHomotopyEquiv (X Y : SSet.{u}) (f : X ⟶ Y) (g : Y ⟶ X)
    (Hleft : SSet.Homotopy (f ≫ g) (𝟙 X))
    (Hright : SSet.Homotopy (g ≫ f) (𝟙 Y)) :
    ⇑((realizedHomotopyEquiv X Y f g Hleft Hright).symm) = ⇑(SSet.toTop.map g).hom :=
  rfl

end SSet
