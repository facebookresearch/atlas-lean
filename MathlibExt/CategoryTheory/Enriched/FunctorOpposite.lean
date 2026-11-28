/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module
public import Mathlib.CategoryTheory.Enriched.Opposite

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uB uV vV
open CategoryTheory MonoidalCategory BraidedCategory Opposite

namespace CategoryTheory.EnrichedFunctor

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [BraidedCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {B : Type uB} [EnrichedCategory V B]

/-- The actual enriched opposite index functor retains every reversed Hom map. -/
def opposite (j : EnrichedFunctor V A B) : EnrichedFunctor V Aᵒᵖ Bᵒᵖ where
  obj a := op (j.obj a.unop)
  map a b := j.map b.unop a.unop
  map_id a := j.map_id a.unop
  map_comp a b c := by
    let P : V := b.unop ⟶[V] a.unop
    let Q : V := c.unop ⟶[V] b.unop
    let P' : V := j.obj b.unop ⟶[V] j.obj a.unop
    let Q' : V := j.obj c.unop ⟶[V] j.obj b.unop
    let f : P ⟶ P' := j.map b.unop a.unop
    let g : Q ⟶ Q' := j.map c.unop b.unop
    have hComp : eComp V c.unop b.unop a.unop ≫ j.map c.unop a.unop =
        (g ⊗ₘ f) ≫ eComp V (j.obj c.unop) (j.obj b.unop) (j.obj a.unop) :=
      j.map_comp c.unop b.unop a.unop
    have hBraid : (β_ P Q).hom ≫ (g ⊗ₘ f) = (f ⊗ₘ g) ≫ (β_ P' Q').hom :=
      (braiding_naturality f g).symm
    change ((β_ P Q).hom ≫ eComp V c.unop b.unop a.unop) ≫
        j.map c.unop a.unop =
      (f ⊗ₘ g) ≫ ((β_ P' Q').hom ≫
        eComp V (j.obj c.unop) (j.obj b.unop) (j.obj a.unop))
    calc
      _ = (β_ P Q).hom ≫
          ((g ⊗ₘ f) ≫ eComp V (j.obj c.unop) (j.obj b.unop) (j.obj a.unop)) :=
        (Category.assoc _ _ _).trans (congrArg (fun z => (β_ P Q).hom ≫ z) hComp)
      _ = ((f ⊗ₘ g) ≫ (β_ P' Q').hom) ≫
          eComp V (j.obj c.unop) (j.obj b.unop) (j.obj a.unop) :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun z => z ≫ eComp V (j.obj c.unop) (j.obj b.unop) (j.obj a.unop)) hBraid)
      _ = _ := Category.assoc _ _ _

/-- The opposite construction keeps the actual original index object. -/
theorem opposite_obj (j : EnrichedFunctor V A B) (a : Aᵒᵖ) :
    (opposite j).obj a = op (j.obj a.unop) := rfl

/-- The full opposite Hom morphism is the original reversed Hom morphism. -/
theorem opposite_map (j : EnrichedFunctor V A B) (a b : Aᵒᵖ) :
    (opposite j).map a b = j.map b.unop a.unop := rfl

end CategoryTheory.EnrichedFunctor
