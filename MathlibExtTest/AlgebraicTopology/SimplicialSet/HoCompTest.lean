/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.HoComp

/-! # Internal composition on homotopy categories of functor objects: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.HoComp`: external
products of edges, internal composition `SSet.hoComp` and its object
and generating-morphism formulas, its slices at a vertex, the
identification of a slice at a classified vertex with
precomposition, and whiskering isomorphisms through composition.
They deliberately do not import Joyal categorical equivalences.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace HoCompTest

section TensorEdges

variable {X Y : SSet.{u}} {x x' : X _⦋0⦌} {y y' : Y _⦋0⦌}

example (e₁ : SSet.Edge x x') (e₂ : SSet.Edge y y') :
    SSet.Edge (X := X ⊗ Y) (x, y) (x', y') :=
  e₁.tensor e₂

example (e₁ : SSet.Edge x x') (e₂ : SSet.Edge y y') :
    (e₁.tensor e₂).edge = (e₁.edge, e₂.edge) :=
  SSet.Edge.tensor_edge e₁ e₂

example (e₁ : SSet.Edge x x') (e₂ : SSet.Edge y y') :
    (e₁.tensor e₂).toTruncated = e₁.toTruncated.tensor e₂.toTruncated :=
  SSet.Edge.toTruncated_tensor e₁ e₂

end TensorEdges

section HoComp

variable {X Y C : SSet.{u}} {f : X ⟶ Y}

example (a : ((ihom X).obj Y) _⦋0⦌) (b : ((ihom Y).obj C) _⦋0⦌) :
    (SSet.hoComp X Y C).obj (SSet.HomotopyCategory.mk a, SSet.HomotopyCategory.mk b) =
      SSet.HomotopyCategory.mk ((MonoidalClosed.comp X Y C).app (op ⦋0⦌) (a, b)) :=
  SSet.hoComp_obj_mk_mk a b

example (g : Y ⟶ C) :
    (MonoidalClosed.comp X Y C).app (op ⦋0⦌)
        (SSet.ihomVertexEquiv X Y f, SSet.ihomVertexEquiv Y C g) =
      SSet.ihomVertexEquiv X C (f ≫ g) :=
  SSet.comp_app_zero_ihomVertexEquiv f g

example : SSet.hoCompSlice (SSet.HomotopyCategory.mk (SSet.ihomVertexEquiv X Y f)) =
    (SSet.hoFunctor.map ((pre f).app C)).toFunctor :=
  SSet.hoCompSlice_mk_ihomVertexEquiv_eq_hoPre f C

example (a : ((ihom X).obj Y) _⦋0⦌) {b₀ b₁ : ((ihom Y).obj C) _⦋0⦌}
    (e : SSet.Edge b₀ b₁) :
    (SSet.hoComp X Y C).map (Prod.mkHom (𝟙 (SSet.HomotopyCategory.mk a))
        (SSet.HomotopyCategory.homMk e)) =
      SSet.HomotopyCategory.homMk (((SSet.Edge.id a).tensor e).map
        (MonoidalClosed.comp X Y C)) :=
  SSet.hoComp_map_mkHom_id_homMk e

example (a : ((ihom X).obj Y) _⦋0⦌) (b : ((ihom Y).obj C) _⦋0⦌) :
    (SSet.hoCompSlice (SSet.HomotopyCategory.mk a)).obj
        (SSet.HomotopyCategory.mk b) =
      SSet.HomotopyCategory.mk ((MonoidalClosed.comp X Y C).app (op ⦋0⦌) (a, b)) :=
  SSet.hoCompSlice_obj_mk a b

example (a : ((ihom X).obj Y) _⦋0⦌) {b₀ b₁ : ((ihom Y).obj C) _⦋0⦌}
    (e : SSet.Edge b₀ b₁) :
    (SSet.hoCompSlice (SSet.HomotopyCategory.mk a)).map
        (SSet.HomotopyCategory.homMk e) =
      SSet.HomotopyCategory.homMk (((SSet.Edge.id a).tensor e).map
        (MonoidalClosed.comp X Y C)) :=
  SSet.hoCompSlice_map_homMk a e

example (b : ((ihom Y).obj C) _⦋0⦌) :
    (MonoidalClosed.comp X Y C).app (op ⦋0⦌) (SSet.ihomVertexEquiv X Y f, b) =
      ((pre f).app C).app (op ⦋0⦌) b :=
  SSet.comp_app_zero_ihomVertexEquiv_pre f b

example {b₀ b₁ : ((ihom Y).obj C) _⦋0⦌} (e : SSet.Edge b₀ b₁) :
    (MonoidalClosed.comp X Y C).app (op ⦋1⦌)
        ((SSet.Edge.id (SSet.ihomVertexEquiv X Y f)).edge, e.edge) =
      ((pre f).app C).app (op ⦋1⦌) e.edge :=
  SSet.comp_app_one_tensor_id_edge f e

example {a₁ a₂ : ((ihom X).obj Y).HomotopyCategory} (α : a₁ ≅ a₂) :
    SSet.hoCompSlice (C := C) a₁ ≅ SSet.hoCompSlice a₂ :=
  SSet.hoCompSliceIso α

end HoComp

end HoCompTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
