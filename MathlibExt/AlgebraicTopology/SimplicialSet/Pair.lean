/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.SSetPair

@[expose] public section

universe u

open CategoryTheory

namespace SSetPair

variable {X Y : SSetPair.{u}}

/-- The first (ambient) simplicial set of the pair. -/
abbrev fst : SSet.{u} := X.right

/-- The second (subobject) simplicial set of the pair. -/
abbrev snd : SSet.{u} := X.left

/-- The inclusion of the second simplicial set into the first. -/
abbrev map : X.snd ⟶ X.fst := X.hom

/-- Construct a morphism in `SSetPair` from its components. -/
abbrev ofHom (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd)
    (w : g ≫ Y.map = X.map ≫ f := by cat_disch) : X ⟶ Y :=
  MorphismProperty.Arrow.homMk g f w

/-- The functor from simplicial pairs to simplicial sets that forgets the second set,
i.e. the projection to the first (ambient) component. -/
abbrev proj₁ : SSetPair.{u} ⥤ SSet.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.rightFunc

/-- The functor from simplicial pairs to simplicial sets that forgets the first set,
i.e. the projection to the second (subobject) component. -/
abbrev proj₂ : SSetPair.{u} ⥤ SSet.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.leftFunc

variable {P P' : SSetPair.{u}}

/-- The ambient component of a morphism of simplicial pairs. -/
abbrev Hom.fst (f : P ⟶ P') : P.fst ⟶ P'.fst := f.hom.right

/-- The subobject component of a morphism of simplicial pairs. -/
abbrev Hom.snd (f : P ⟶ P') : P.snd ⟶ P'.snd := f.hom.left

@[reassoc, elementwise]
lemma Hom.w (f : P ⟶ P') : Hom.snd f ≫ P'.map = P.map ≫ Hom.fst f := f.hom.w

end SSetPair
