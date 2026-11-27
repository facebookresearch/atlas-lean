/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarCategory
public import Mathlib.CategoryTheory.Category.Cat

/-!
# Whole original canonical scalar functor laws in independent universes

The canonical ScalarObject, scalarOperator and scalarFunctor retain the
original objects and every full Hom simplex. Their actual whole functor
laws hold with independent source/target object and coefficient universes.
The complete canonical scalar category diagram then retains these SAME
original maps in every degree.
-/

@[expose] public section

noncomputable section
universe u v w z
open CategoryTheory

namespace SSet

variable {C : Type v} [EnrichedCategory SSet.{u} C]
  {D : Type w} [EnrichedCategory SSet.{u} D] {E : Type z} [EnrichedCategory SSet.{u} E]

/-- The entire SAME original canonical scalar identity operator is the actual identity functor. -/
theorem scalarOperator_id (q : SimplexCategoryᵒᵖ) :
    scalarOperator (C := C) (𝟙 q) = 𝟭 (ScalarObject C q) := by
  refine Functor.hext (F := scalarOperator (C := C) (𝟙 q))
    (G := 𝟭 (ScalarObject C q)) (fun x => rfl) ?_
  intro x y a
  apply heq_of_eq
  exact Functor.map_id_apply (x.obj ⟶[SSet.{u}] y.obj) q a

/-- The whole original canonical composite operator is the composite of the SAME supplied
scalar maps. -/
theorem scalarOperator_comp {q r s : SimplexCategoryᵒᵖ} (f : q ⟶ r) (g : r ⟶ s) :
    scalarOperator (C := C) (f ≫ g) = scalarOperator (C := C) f ⋙ scalarOperator (C := C) g := by
  refine Functor.hext (F := scalarOperator (C := C) (f ≫ g))
    (G := scalarOperator (C := C) f ⋙ scalarOperator (C := C) g) (fun x => rfl) ?_
  intro x y a
  apply heq_of_eq
  exact Functor.map_comp_apply (x.obj ⟶[SSet.{u}] y.obj) f g a

/-- The SAME original enriched identity gives the whole canonical scalar identity functor. -/
theorem scalarFunctor_id (q : SimplexCategoryᵒᵖ) :
    scalarFunctor (EnrichedFunctor.id SSet.{u} C) q = 𝟭 (ScalarObject C q) := rfl

/-- The complete canonical scalar map retains actual enriched composition at all independent
original universes. -/
theorem scalarFunctor_comp (F : EnrichedFunctor SSet.{u} C D) (G : EnrichedFunctor SSet.{u} D E)
    (q : SimplexCategoryᵒᵖ) : scalarFunctor (F.comp SSet.{u} G) q =
      scalarFunctor F q ⋙ scalarFunctor G q := rfl

/-- Both full canonical scalar functors retain the SAME original Hom naturality and
individual object maps. -/
theorem scalarFunctor_operator (F : EnrichedFunctor SSet.{u} C D)
    {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    scalarOperator (C := C) f ⋙ scalarFunctor F r =
      scalarFunctor F q ⋙ scalarOperator (C := D) f := by
  refine Functor.hext (F := scalarOperator (C := C) f ⋙ scalarFunctor F r)
    (G := scalarFunctor F q ⋙ scalarOperator (C := D) f) (fun x => rfl) ?_
  intro x y a
  exact heq_of_eq (NatTrans.naturality_apply (F.map x.obj y.obj) f a)

/-- The SAME canonical scalar category diagram retains an arbitrary independent original
object universe. -/
def scalarCategoryDiagramUniverse (C : Type v) [EnrichedCategory SSet.{u} C] :
    SimplexCategoryᵒᵖ ⥤ Cat.{u, v} where
  obj q := Cat.of (ScalarObject C q)
  map f := (scalarOperator (C := C) f).toCatHom
  map_id q := by
    apply Cat.ext
    exact scalarOperator_id q
  map_comp f g := by
    apply Cat.ext
    exact scalarOperator_comp f g

/-- The SAME whole canonical scalar category map uses every original enriched Hom and object map. -/
def scalarCategoryMapUniverse {D' : Type v} [EnrichedCategory SSet.{u} D']
    (F : EnrichedFunctor SSet.{u} C D') :
    scalarCategoryDiagramUniverse C ⟶ scalarCategoryDiagramUniverse D' where
  app q := (scalarFunctor F q).toCatHom
  naturality q r f := by
    apply Cat.ext
    exact scalarFunctor_operator F f

end SSet
