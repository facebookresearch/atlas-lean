/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeYoneda
public import Mathlib.CategoryTheory.InducedCategory
public import MathlibExt.CategoryTheory.Enriched.PointFunctionTransport

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uJ uC vC

open CategoryTheory MonoidalCategory Opposite
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.FreeMappingSource

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} {J : Type uJ} [EnrichedCategory V J]
  {C : Type uC} [Category.{vC} C]
  (index : A → J) (F : A → C) (U : C ⥤ EnrichedFunctorCat V J)
  (q : ∀ a, U.obj (F a) ≅ Free.object (index a) (𝟙_ V))

/-- Every complete original opposite module map transports through actual free comparisons. -/
@[no_expose]
def freeMap {a b : A} (f : op (F a) ⟶ op (F b)) :
    Free.object (index b) (𝟙_ V) ⟶ Free.object (index a) (𝟙_ V) :=
  (q b).inv ≫ U.map f.unop ≫ (q a).hom

/-- Actual opposite free-map identities retain every original comparison component. -/
theorem freeMap_id (a : A) : freeMap index F U q (𝟙 (op (F a))) = 𝟙 _ := by
  unfold freeMap
  rw [unop_id, U.map_id, Category.id_comp, Iso.inv_hom_id]

/-- Actual opposite free-map composition keeps both original module maps in source order. -/
theorem freeMap_comp {a b c : A} (f : op (F a) ⟶ op (F b))
    (g : op (F b) ⟶ op (F c)) :
    freeMap index F U q (f ≫ g) = freeMap index F U q g ≫ freeMap index F U q f := by
  simp only [freeMap, unop_comp, U.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Genuine source comparison on all original unit-Hom arrows. -/
@[no_expose]
def functor : InducedCategory Cᵒᵖ (fun a => op (F a)) ⥤ ForgetEnrichment V J where
  obj a := ForgetEnrichment.of V (index a)
  map {a b} f := ForgetEnrichment.homOf V
    (FreeYoneda.evaluateHom (index a) (index b) (freeMap index F U q f.hom))
  map_id a := by
    rw [InducedCategory.id_hom, freeMap_id, FreeYoneda.evaluateHom_id]
    exact ForgetEnrichment.homOf_eId V (index a)
  map_comp {a b c} f g := by
    rw [InducedCategory.comp_hom, freeMap_comp, FreeYoneda.evaluateHom_comp]
    exact ForgetEnrichment.homOf_comp V _ _

/-- Every source object retains its actual original degree label. -/
theorem functor_obj (a : A) :
    (functor index F U q).obj a = ForgetEnrichment.of V (index a) := by rfl

/-- Every source arrow retains its complete original module map and free evaluation. -/
theorem functor_map {a b : A}
    (f : InducedCategory.Hom (F := fun a => op (F a)) a b) :
    HEq ((functor index F U q).map f)
      (ForgetEnrichment.homOf V
        (FreeYoneda.evaluateHom (index a) (index b)
          ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom))) := by rfl

/-- The entire original functor map uses the same full projected and reversed module arrow. -/
theorem functor_map_function (a b : A) :
    HEq (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
      (functor index F U q).map f)
        (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
          ForgetEnrichment.homOf V
            (FreeYoneda.evaluateHom (index a) (index b)
              ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom))) := by rfl

/-- The whole original point function is the full free evaluation of the original arrow. -/
theorem functor_point_function (a b : A) :
    HEq (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
      ForgetEnrichment.homTo V ((functor index F U q).map f))
        (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
          FreeYoneda.evaluateHom (index a) (index b)
            ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom)) := by rfl

/-- Every original unit point is the full source-first free-evaluation coend point. -/
theorem functor_point {a b : A}
    (f : InducedCategory.Hom (F := fun a => op (F a)) a b) :
    HEq (ForgetEnrichment.homTo V ((functor index F U q).map f))
      (FreeYoneda.evaluateHom (index a) (index b)
        ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom)) := by rfl

/-- The functor's entire Hom endpoint is the original Hom at its actual object labels. -/
theorem functor_hom_eq (a b : A) :
    (ForgetEnrichment.to V ((functor index F U q).obj a) ⟶[V]
      ForgetEnrichment.to V ((functor index F U q).obj b)) =
        (index a ⟶[V] index b) := by
  rw [functor_obj, functor_obj]
  rfl

/-- The entire original point function rebases through its proved original object fields. -/
theorem functor_point_function_rebased (a b : A) :
    (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
      ForgetEnrichment.homTo V ((functor index F U q).map f) ≫
        eqToHom (functor_hom_eq index F U q a b)) =
          (fun f : InducedCategory.Hom (F := fun a => op (F a)) a b =>
            FreeYoneda.evaluateHom (index a) (index b)
              ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom)) := by
  exact EnrichedPointFunctionTransport.point_function
    (functor_hom_eq index F U q a b) _ _ (functor_point_function index F U q a b)

/-- Each original point retains the same actual object-field transport and full free map. -/
@[reassoc]
theorem functor_point_rebased {a b : A}
    (f : InducedCategory.Hom (F := fun a => op (F a)) a b) :
    ForgetEnrichment.homTo V ((functor index F U q).map f) ≫
      eqToHom (functor_hom_eq index F U q a b) =
        FreeYoneda.evaluateHom (index a) (index b)
          ((q b).inv ≫ U.map f.hom.unop ≫ (q a).hom) := by
  exact congrFun (functor_point_function_rebased index F U q a b) f

end CategoryTheory.EnrichedFunctorCat.FreeMappingSource
