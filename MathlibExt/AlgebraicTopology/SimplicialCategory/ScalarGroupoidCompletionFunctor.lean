/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionUnit

/-!
# The canonical scalar groupoid-completion functor and unit

The same enriched functor gives the native
completion map at every canonical scalar degree. Full Hom maps,
individual object maps, ordinal operators and enriched
Identity/composition all remain. The full unit square is
natural as an enriched functor equality, not a weak-map premise.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion

variable {C D E : Carrier.{u}}

/-- Each same canonical scalar functor gives its native
groupoid-completion map. -/
def scalarMap (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) : category C q ⥤ category D q :=
  FreeGroupoid.map (SSet.scalarFunctor F q)

/-- The same individual object is mapped by the enriched object map. -/
theorem scalarMap_vertex (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) (x : C) :
    (scalarMap F q).obj (vertex C q x) = vertex D q (F.obj x) := rfl

/-- Canonical scalar naturality is retained by native completion functors. -/
theorem scalarMap_operator (F : C ⟶ D) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    operator C f ⋙ scalarMap F r = scalarMap F q ⋙ operator D f := by
  unfold operator scalarMap
  exact (FreeGroupoid.map_comp _ _).symm.trans
    ((congrArg FreeGroupoid.map (SSet.scalarFunctor_operator F f)).trans
      (FreeGroupoid.map_comp _ _))

/-- The same native completion Hom map retains all scalar degrees and operators. -/
def mapHomMap (F : C ⟶ D) (x y : C) : hom C x y ⟶ hom D (F.obj x) (F.obj y) where
  app q := ↾fun a => (scalarMap F q).map a
  naturality q r f := by
    ext a
    exact eq_of_heq (Functor.hcongr_hom (scalarMap_operator F f) a)

/-- The enriched functor induces the full completion functor with its
same object map. -/
def map (F : C ⟶ D) : object C ⟶ object D where
  obj := F.obj
  map := mapHomMap F
  map_id x := by
    ext q a
    exact (scalarMap F q).map_id (vertex C q x)
  map_comp x y z := by
    ext q a
    exact (scalarMap F q).map_comp a.1 a.2

/-- The completion map retains every same individual object image literally. -/
theorem map_obj (F : C ⟶ D) (x : C) : (map F).obj x = F.obj x := rfl

/-- Every completion Hom map is the same native scalar functor map in
each degree. -/
theorem map_apply (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) (x y : C) (a : (hom C x y).obj q) :
    ((map F).map x y).app q a = (scalarMap F q).map a := rfl

/-- Native completion keeps the same scalar identity functor. -/
theorem scalarMap_id (q : SimplexCategoryᵒᵖ) : scalarMap (𝟙 C) q = 𝟭 (category C q) := by
  exact (congrArg FreeGroupoid.map (SSet.scalarFunctor_id (C := C) q)).trans (FreeGroupoid.map_id _)

/-- Native completion keeps the same two scalar functors under composition. -/
theorem scalarMap_comp (F : C ⟶ D) (G : D ⟶ E) (q : SimplexCategoryᵒᵖ) :
    scalarMap (F ≫ G) q = scalarMap F q ⋙ scalarMap G q := by
  exact (congrArg FreeGroupoid.map (SSet.scalarFunctor_comp F G q)).trans
    (FreeGroupoid.map_comp _ _)

/-- The same completion of the enriched identity is the enriched identity. -/
theorem map_id (C : Carrier.{u}) : map (𝟙 C) = 𝟙 (object C) := by
  change @EnrichedFunctor.mk SSet.{u} inferInstance inferInstance (object C) inferInstance
    (object C) inferInstance (fun x => x) _ _ _ =
      @EnrichedFunctor.mk SSet.{u} inferInstance inferInstance (object C) inferInstance
        (object C) inferInstance (fun x => x) _ _ _
  congr 1
  funext x y
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro a
  exact eq_of_heq (Functor.hcongr_hom (scalarMap_id q) a)

/-- The completion functor preserves the same enriched composition. -/
theorem map_comp (F : C ⟶ D) (G : D ⟶ E) : map (F ≫ G) = map F ≫ map G := by
  change @EnrichedFunctor.mk SSet.{u} inferInstance inferInstance (object C) inferInstance
    (object E) inferInstance (fun x => G.obj (F.obj x)) _ _ _ =
      @EnrichedFunctor.mk SSet.{u} inferInstance inferInstance (object C) inferInstance
        (object E) inferInstance (fun x => G.obj (F.obj x)) _ _ _
  congr 1
  funext x y
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro a
  exact eq_of_heq (Functor.hcongr_hom (scalarMap_comp F G q) a)

/-- The completion functor on the full varying-object carrier. -/
def functor : Carrier.{u} ⥤ Carrier.{u} where
  obj := object
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The same native full unit commutes with each enriched source map. -/
theorem unit_naturality (F : C ⟶ D) : unit C ≫ map F = F ≫ unit D := by
  change @EnrichedFunctor.mk SSet.{u} inferInstance inferInstance C inferInstance
    (object D) inferInstance F.obj _ _ _ =
      @EnrichedFunctor.mk SSet.{u} inferInstance inferInstance C inferInstance
        (object D) inferInstance F.obj _ _ _
  congr 1

/-- The unit is a natural transformation of the same full enriched
carrier. -/
def naturalUnit : 𝟭 Carrier.{u} ⟶ functor where
  app := unit
  naturality _ _ F := (unit_naturality F).symm

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
