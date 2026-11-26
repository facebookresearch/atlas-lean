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

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Connected

/-!
# Connected cocones in an under category

Let J be a connected category, C any category and D : J ⥤ Under I a diagram of arrows out of
an object I. For a cocone s over the underlying diagram in C, the composites I → D(j) → s.pt
agree for every j. They therefore define a single arrow I → s.pt.

This arrow makes s.pt an object of Under I, and the existing legs s.ι_j form a cocone there.
The construction keeps the underlying vertex and all legs of s; it applies to every cocone,
without requiring a colimit. The indexing and coefficient object and morphism universes are
independent.
-/

@[expose] public section

noncomputable section

universe v u w w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J] [IsConnected J]

/-- Lifting a connected cocone to an under category.

Let D : J ⥤ Under I with J connected, and let s be a cocone over D followed by the forgetful
functor to C. Give s.pt the arrow I → s.pt obtained as D(j).hom ≫ s.ι_j at any j.
Connectedness makes this composite independent of j, so the same vertex and legs define a
cocone over D in Under I. -/
def liftConnectedUnderCocone (I : C) {D : J ⥤ Under I}
    (s : Cocone (D ⋙ Under.forget I)) : Cocone D where
  pt := Under.mk ((D.obj (Classical.arbitrary J)).hom ≫ s.ι.app (Classical.arbitrary J))
  ι.app j := Under.homMk (s.ι.app j) <| by
    apply constant_of_preserves_morphisms (fun i => (D.obj i).hom ≫ s.ι.app i) _ j
    intro a b f
    change (D.obj a).hom ≫ s.ι.app a = (D.obj b).hom ≫ s.ι.app b
    have h : (D.map f).right ≫ s.ι.app b = s.ι.app a := s.w f
    rw [← h, ← Category.assoc, Under.w (D.map f)]
  ι.naturality a b f := by
    apply Under.UnderMorphism.ext
    change (D.map f).right ≫ s.ι.app b = s.ι.app a ≫ 𝟙 s.pt
    exact (s.w f).trans (Category.comp_id (s.ι.app a)).symm

end CategoryTheory.Limits
