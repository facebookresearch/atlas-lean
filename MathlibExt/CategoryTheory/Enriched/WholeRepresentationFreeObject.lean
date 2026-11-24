/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Enriched.WholeRepresentationData
public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation

/-!
# The original free object as a whole enriched representation

The whole Hom object gives the actual coefficient-tensor-Hom object.
Its full action, unit and associativity use the original enriched free
producers. The construction itself only needs a monoidal base.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV uC

open CategoryTheory MonoidalCategory

namespace CategoryTheory.WholeRepresentation.FreeEvaluation

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [EnrichedCategory V C]

/-- The actual original coefficient-tensor-Hom object and complete enriched action. -/
def freeObject (n : C) (K : V) : WholeRepresentation V C where
  obj k := K ⊗ (n ⟶[V] k)
  action := EnrichedFunctorCat.Free.action n K
  unit := EnrichedFunctorCat.Free.action_id n K
  assoc k l m := (EnrichedFunctorCat.Free.action_comp n K k l m).symm

/-- The actual full tensor morphism on a coefficient at every enriched object. -/
def freeMap (n : C) {K L : V} (h : K ⟶ L) : freeObject n K ⟶ freeObject n L where
  app k := h ▷ (n ⟶[V] k)
  comm k l := (EnrichedFunctorCat.Free.coefficientMap_natural n h k l).symm

/-- The free functor retains the actual original tensor morphisms of every coefficient. -/
def freeAt (n : C) : V ⥤ WholeRepresentation V C where
  obj := freeObject n
  map := freeMap n
  map_id K := by
    apply hom_ext
    intro k
    exact id_whiskerRight _ _
  map_comp f g := by
    apply hom_ext
    intro k
    exact comp_whiskerRight _ _ _

/-- Evaluation retains the original whole value object and each original component. -/
def evaluation (n : C) : WholeRepresentation V C ⥤ V where
  obj X := X.obj n
  map f := f.app n
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The free object retains the complete original coefficient-tensor-Hom formula. -/
theorem freeObject_obj (n k : C) (K : V) : (freeObject n K).obj k = K ⊗ (n ⟶[V] k) := rfl

/-- The free action is the actual original associator followed by enriched composition. -/
theorem freeObject_action (n k l : C) (K : V) :
    (freeObject n K).action k l = (α_ K (n ⟶[V] k) (k ⟶[V] l)).hom ≫ K ◁ eComp V n k l := rfl

/-- Every coefficient morphism retains its entire tensor component. -/
theorem freeAt_map_app (n k : C) {K L : V} (h : K ⟶ L) :
    ((freeAt n).map h).app k = h ▷ (n ⟶[V] k) := rfl

/-- Evaluation keeps every original object. -/
theorem evaluation_obj (n : C) (X : WholeRepresentation V C) :
    (evaluation n).obj X = X.obj n := rfl

/-- Evaluation keeps every original morphism component. -/
theorem evaluation_map (n : C) {X Y : WholeRepresentation V C} (f : X ⟶ Y) :
    (evaluation n).map f = f.app n := rfl

end CategoryTheory.WholeRepresentation.FreeEvaluation
