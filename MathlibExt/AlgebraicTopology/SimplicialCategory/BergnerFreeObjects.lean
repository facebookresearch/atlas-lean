/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerObjectLifting
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierSmallColimits
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Genuine free original objects in the varying-object enriched category

Take the actual coproduct of original one-object unit-Hom enrichments.
Its whole enriched universal property represents arbitrary functions into
the SAME individual object type of a target. Both inverses, object
readbacks and source/target naturality retain the full enriched maps.
This is the object-adding stage of the global C0 factorization in the
proof of HTT Proposition A.3.2.4, rather than a model/QE certificate.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.BergnerFreeObjects

/-- The genuine varying-object coproduct of one original unit-Hom object per supplied label. -/
def object (O : Type u) : Carrier.{u} := ∐ fun _ : O => BergnerObjects.point.{u}

/-- The actual whole one-object coproduct injection at a supplied individual label. -/
def injection (O : Type u) (x : O) : BergnerObjects.point.{u} ⟶ object O :=
  Sigma.ι (fun _ : O => BergnerObjects.point.{u}) x

/-- The individual original object read from that entire one-object injection. -/
def vertex (O : Type u) (x : O) : object O := (injection O x).obj PUnit.unit

/-- Extend the supplied original object function to the whole actual coproduct functor. -/
def desc (O : Type u) {C : Carrier.{u}} (a : O → C) : object O ⟶ C :=
  Sigma.desc (fun x => BergnerObjects.select (a x))

/-- Every full original one-object injection has its exact supplied whole extension. -/
theorem injection_desc (O : Type u) {C : Carrier.{u}} (a : O → C) (x : O) :
    injection O x ≫ desc O a = BergnerObjects.select (a x) :=
  Sigma.ι_desc _ _

/-- Extension carries each original label vertex to the SAME prescribed individual object. -/
@[simp]
theorem desc_vertex (O : Type u) {C : Carrier.{u}} (a : O → C) (x : O) :
    (desc O a).obj (vertex O x) = a x :=
  congrArg (fun F : BergnerObjects.point.{u} ⟶ C => F.obj PUnit.unit) (injection_desc O a x)

/-- Whole original target composition is determined by the same prescribed object composition. -/
theorem desc_comp (O : Type u) {C D : Carrier.{u}} (a : O → C) (F : C ⟶ D) :
    desc O a ≫ F = desc O (F.obj ∘ a) := by
  apply Sigma.hom_ext
  intro x
  change injection O x ≫ (desc O a ≫ F) = injection O x ≫ desc O (F.obj ∘ a)
  rw [← Category.assoc, injection_desc, injection_desc]
  exact BergnerObjects.select_comp (a x) F

/-- Every entire original enriched map from this coproduct is recovered from all its label vertices. -/
theorem desc_readback (O : Type u) {C : Carrier.{u}} (F : object O ⟶ C) :
    desc O (fun x => F.obj (vertex O x)) = F := by
  apply Sigma.hom_ext
  intro x
  change injection O x ≫ desc O (fun x => F.obj (vertex O x)) = injection O x ≫ F
  rw [injection_desc]
  exact BergnerObjects.select_readback (injection O x ≫ F)

/-- Both genuine inverses identify full enriched maps with functions into the SAME original object type. -/
def homEquiv (O : Type u) (C : Carrier.{u}) : (object O ⟶ C) ≃ (O → C) where
  toFun F x := F.obj (vertex O x)
  invFun := desc O
  left_inv := desc_readback O
  right_inv a := funext (desc_vertex O a)

/-- Freely extend a supplied original label function to the full changing-object enrichment. -/
def map {O P : Type u} (f : O → P) : object O ⟶ object P := desc O (vertex P ∘ f)

/-- The whole original free-object map reads its label function literally at every original vertex. -/
@[simp]
theorem map_vertex {O P : Type u} (f : O → P) (x : O) :
    (map f).obj (vertex O x) = vertex P (f x) := desc_vertex O _ x

/-- The same original free-object identity is the whole enriched identity. -/
theorem map_id (O : Type u) : map (id : O → O) = 𝟙 (object O) :=
  desc_readback O (𝟙 (object O))

/-- Full original label extensions preserve the supplied composition without changing either map. -/
theorem map_comp {O P Q : Type u} (f : O → P) (g : P → Q) : map (g ∘ f) = map f ≫ map g := by
  apply (homEquiv O (object Q)).injective
  funext x
  change (map (g ∘ f)).obj (vertex O x) = (map g).obj ((map f).obj (vertex O x))
  simp only [map_vertex, Function.comp_apply]

/-- The genuine free-object functor on original labels and their entire original maps. -/
def functor : Type u ⥤ Carrier.{u} where
  obj := object
  map f := map f
  map_id := map_id
  map_comp f g := map_comp f g

/-- Original source precomposition is the same entire free-object map followed by extension. -/
theorem desc_precompose {O P : Type u} {C : Carrier.{u}} (f : O → P) (a : P → C) :
    desc O (a ∘ f) = map f ≫ desc P a := by
  apply (homEquiv O C).injective
  funext x
  change (desc O (a ∘ f)).obj (vertex O x) = (desc P a).obj ((map f).obj (vertex O x))
  simp only [desc_vertex, map_vertex, Function.comp_apply]

/-- The actual free-object/object-forgetting adjunction on the original changing-object carrier. -/
def adjunction : functor.{u} ⊣ forgetObjects.{u} :=
  Adjunction.mkOfHomEquiv {
    homEquiv O C := (homEquiv O C).trans TypeCat.homEquiv.symm
    homEquiv_naturality_left_symm := fun f g => desc_precompose f g
    homEquiv_naturality_right := fun F G => by
      apply ConcreteCategory.hom_ext
      intro x
      rfl }

/-- The actual unit reads each supplied individual label to its SAME original coproduct vertex. -/
theorem unit_app (O : Type u) : (adjunction.{u}).unit.app O = ↾vertex O := rfl

/-- The genuine counit evaluates every original one-object summand at its SAME individual target object. -/
theorem counit_app (C : Carrier.{u}) : (adjunction.{u}).counit.app C = desc (C : Type u) id := rfl

/-- The actual counit is literally surjective on the original objects. -/
theorem counit_objects_surjective (C : Carrier.{u}) :
    Function.Surjective ((adjunction.{u}).counit.app C).obj := by
  intro x
  exact ⟨vertex (C : Type u) x, desc_vertex (C : Type u) id x⟩

end CategoryTheory.SimplicialEnrichment.BergnerFreeObjects
