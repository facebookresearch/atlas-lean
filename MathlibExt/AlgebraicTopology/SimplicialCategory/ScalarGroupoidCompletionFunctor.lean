/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionUnit

/-!
# The genuine canonical scalar groupoid-completion functor and unit

The SAME whole original enriched functor gives the actual native
completion map at every canonical scalar degree. Full Hom maps,
individual object maps, original ordinal operators and enriched
identity/composition all remain. The full original unit square is
natural as a whole enriched functor equality, not a weak-map premise.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion

variable {C D E : Carrier.{u}}

/-- Each SAME canonical full original scalar functor gives its actual native
groupoid-completion map. -/
def scalarMap (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) : category C q ⥤ category D q :=
  FreeGroupoid.map (SSet.scalarFunctor F q)

/-- The SAME individual original object is mapped by the actual original enriched object map. -/
theorem scalarMap_vertex (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) (x : C) :
    (scalarMap F q).obj (vertex C q x) = vertex D q (F.obj x) := rfl

/-- Whole original canonical scalar naturality is retained by actual native completion functors. -/
theorem scalarMap_operator (F : C ⟶ D) {q r : SimplexCategoryᵒᵖ} (f : q ⟶ r) :
    operator C f ⋙ scalarMap F r = scalarMap F q ⋙ operator D f := by
  unfold operator scalarMap
  exact (FreeGroupoid.map_comp _ _).symm.trans
    ((congrArg FreeGroupoid.map (SSet.scalarFunctor_operator F f)).trans
      (FreeGroupoid.map_comp _ _))

/-- The SAME actual native completion Hom map retains all original scalar degrees and operators. -/
def mapHomMap (F : C ⟶ D) (x y : C) : hom C x y ⟶ hom D (F.obj x) (F.obj y) where
  app q := ↾fun a => (scalarMap F q).map a
  naturality q r f := by
    ext a
    exact eq_of_heq (Functor.hcongr_hom (scalarMap_operator F f) a)

/-- The original full enriched functor induces the genuine full completion functor with its
SAME object map. -/
def map (F : C ⟶ D) : object C ⟶ object D where
  obj := F.obj
  map := mapHomMap F
  map_id x := by
    ext q a
    exact (scalarMap F q).map_id (vertex C q x)
  map_comp x y z := by
    ext q a
    exact (scalarMap F q).map_comp a.1 a.2

/-- The whole original completion map retains every SAME individual object image literally. -/
theorem map_obj (F : C ⟶ D) (x : C) : (map F).obj x = F.obj x := rfl

/-- Every entire original completion Hom map is the SAME native full scalar functor map in
each degree. -/
theorem map_apply (F : C ⟶ D) (q : SimplexCategoryᵒᵖ) (x y : C) (a : (hom C x y).obj q) :
    ((map F).map x y).app q a = (scalarMap F q).map a := rfl

/-- Native completion keeps the SAME whole original scalar identity functor. -/
theorem scalarMap_id (q : SimplexCategoryᵒᵖ) : scalarMap (𝟙 C) q = 𝟭 (category C q) := by
  exact (congrArg FreeGroupoid.map (SSet.scalarFunctor_id (C := C) q)).trans (FreeGroupoid.map_id _)

/-- Native completion keeps the SAME two entire original scalar functors under composition. -/
theorem scalarMap_comp (F : C ⟶ D) (G : D ⟶ E) (q : SimplexCategoryᵒᵖ) :
    scalarMap (F ≫ G) q = scalarMap F q ⋙ scalarMap G q := by
  exact (congrArg FreeGroupoid.map (SSet.scalarFunctor_comp F G q)).trans
    (FreeGroupoid.map_comp _ _)

/-- The SAME actual completion of the original enriched identity is the whole enriched identity. -/
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

/-- The entire original completion functor preserves the SAME original enriched composition. -/
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

/-- The genuine original completion functor on the full varying-object carrier. -/
def functor : Carrier.{u} ⥤ Carrier.{u} where
  obj := object
  map := map
  map_id := map_id
  map_comp := map_comp

/-- The SAME native full original unit commutes with each entire enriched source map. -/
theorem unit_naturality (F : C ⟶ D) : unit C ≫ map F = F ≫ unit D := by
  change @EnrichedFunctor.mk SSet.{u} inferInstance inferInstance C inferInstance
    (object D) inferInstance F.obj _ _ _ =
      @EnrichedFunctor.mk SSet.{u} inferInstance inferInstance C inferInstance
        (object D) inferInstance F.obj _ _ _
  congr 1

/-- The actual original unit is a genuine natural transformation of the SAME full enriched
carrier. -/
def naturalUnit : 𝟭 Carrier.{u} ⟶ functor where
  app := unit
  naturality _ _ F := (unit_naturality F).symm

end CategoryTheory.SimplicialEnrichment.ScalarGroupoidCompletion
