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
# Literal cocone lifts in an under category

A connected diagram under a fixed object admits a lift of any target cocone.
The lift keeps the supplied vertex and legs. Its source arrow is the common
composite along any cocone leg.
-/

@[expose] public section

noncomputable section

universe v u w w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [Category.{w'} J] [IsConnected J]

/-- Lift a connected target cocone in an under-category with the original vertex and legs. -/
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
