/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# The ordinary category at a scalar simplex

Evaluate each original enriched Hom, identity and composition at one
scalar simplex. Original simplex operators and strict enriched functors
give ordinary functors between these categories. The object labels and
the enriched Hom universe are retained independently.
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory

namespace SSet

/-- The unchanged object label at a specified scalar simplex. -/
structure ScalarObject (C : Type v) [EnrichedCategory SSet.{u} C]
    (Δ : SimplexCategoryᵒᵖ) where
  /-- The original enriched object. -/
  obj : C

variable {C : Type v} [EnrichedCategory SSet.{u} C]
  {D : Type w} [EnrichedCategory SSet.{u} D]

/-- The ordinary category formed by the original evaluated enriched structure maps. -/
instance (Δ : SimplexCategoryᵒᵖ) : Category.{u} (ScalarObject C Δ) where
  Hom x y := (x.obj ⟶[SSet.{u}] y.obj).obj Δ
  id x := (eId SSet.{u} x.obj).app Δ PUnit.unit
  comp f g := (eComp SSet.{u} _ _ _).app Δ ⟨f, g⟩
  id_comp f := by
    exact congrArg (fun q => q.app Δ f) (e_id_comp SSet.{u} _ _)
  comp_id f := by
    exact congrArg (fun q => q.app Δ f) (e_comp_id SSet.{u} _ _)
  assoc f g h := by
    exact congrArg (fun q => q.app Δ ⟨f, g, h⟩) (e_assoc SSet.{u} _ _ _ _)

/-- The ordinary functor induced by one original scalar simplex operator. -/
def scalarOperator {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    ScalarObject C Δ ⥤ ScalarObject C Δ' where
  obj x := ⟨x.obj⟩
  map {x y} f := (x.obj ⟶[SSet.{u}] y.obj).map θ f
  map_id x := (NatTrans.naturality_apply (eId SSet.{u} x.obj) θ PUnit.unit).symm
  map_comp f g := (NatTrans.naturality_apply (eComp SSet.{u} _ _ _) θ ⟨f, g⟩).symm

/-- The ordinary functor uses the literal local Hom maps of a strict enriched functor. -/
def scalarFunctor (P : EnrichedFunctor SSet.{u} C D) (Δ : SimplexCategoryᵒᵖ) :
    ScalarObject C Δ ⥤ ScalarObject D Δ where
  obj x := ⟨P.obj x.obj⟩
  map {x y} f := (P.map x.obj y.obj).app Δ f
  map_id x := congrArg (fun q => q.app Δ PUnit.unit) (P.map_id x.obj)
  map_comp f g := congrArg (fun q => q.app Δ ⟨f, g⟩) (P.map_comp _ _ _)

end SSet
