/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjects
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The actual codiscrete enrichment on original objects

Every Hom is the literal scalar tensor unit. The original object
function determines each whole enriched map into this carrier, giving
a genuine right adjoint to object forgetting. Its unit need not be
weak; it retains objects while sending Hom simplices to the unit.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.CodiscreteEnrichment

private theorem unitHom_eq {X : SSet.{u}} (f g : X ⟶ 𝟙_ SSet.{u}) : f = g := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro x
  change @Eq PUnit.{u + 1} _ _
  exact Subsingleton.elim _ _

/-- The actual unique scalar map to the tensor unit, on every original simplex. -/
def toUnit (X : SSet.{u}) : X ⟶ 𝟙_ SSet.{u} where
  app _ := ↾fun _ => PUnit.unit
  naturality _ _ _ := by
    apply ConcreteCategory.hom_ext
    intro x
    change @Eq PUnit.{u + 1} _ _
    exact Subsingleton.elim _ _

/-- The literal unit-Hom enrichment on the supplied original labels. -/
@[instance_reducible]
def enrichment (O : Type u) : EnrichedCategory SSet.{u} O where
  Hom _ _ := 𝟙_ SSet.{u}
  id _ := 𝟙 _
  comp _ _ _ := (λ_ (𝟙_ SSet.{u})).hom
  id_comp _ _ := unitHom_eq _ _
  comp_id _ _ := unitHom_eq _ _
  assoc _ _ _ _ := unitHom_eq _ _

/-- The actual codiscrete enriched carrier retains the exact supplied object type. -/
def object (O : Type u) : Carrier.{u} := by
  let _ : EnrichedCategory SSet.{u} O := enrichment O
  exact SimplicialEnrichment.of O

/-- The same original object function acts on the literal unit Homs. -/
def map {O P : Type u} (f : O ⟶ P) : object O ⟶ object P where
  obj x := f x
  map _ _ := 𝟙 _
  map_id _ := unitHom_eq _ _
  map_comp _ _ _ := unitHom_eq _ _

/-- The actual codiscrete enriched functor, with full original identity and composition laws. -/
def functor : Type u ⥤ Carrier.{u} where
  obj := object
  map := map
  map_id O := by
    apply EnrichedFunctor.ext SSet.{u} (F := map (𝟙 O)) (G := 𝟙 (object O)) (fun _ => rfl)
    intro x y
    exact unitHom_eq _ _
  map_comp f g := by
    apply EnrichedFunctor.ext SSet.{u} (F := map (f ≫ g)) (G := map f ≫ map g) (fun _ => rfl)
    intro x y
    exact unitHom_eq _ _

/-- Extend the original object function by the actual unique maps to unit Homs. -/
def extend (C : Carrier.{u}) (O : Type u) (f : (C : Type u) ⟶ O) : C ⟶ object O where
  obj x := f x
  map x y := toUnit (x ⟶[SSet.{u}] y)
  map_id _ := unitHom_eq _ _
  map_comp _ _ _ := unitHom_eq _ _

/-- Whole maps into the codiscrete enrichment are exactly original object functions. -/
def homEquiv (C : Carrier.{u}) (O : Type u) : (C ⟶ object O) ≃ ((C : Type u) ⟶ O) where
  toFun F := ↾F.obj
  invFun := extend C O
  left_inv F := by
    apply EnrichedFunctor.ext SSet.{u} (F := extend C O (↾F.obj)) (G := F) (fun _ => rfl)
    intro x y
    exact unitHom_eq _ _
  right_inv _ := rfl

/-- Restriction retains the identical original source object function under whole enriched
composition. -/
theorem homEquiv_source {C D : Carrier.{u}} (F : C ⟶ D) (O : Type u) (G : D ⟶ object O) :
    homEquiv C O (F ≫ G) = forgetObjects.map F ≫ homEquiv D O G := rfl

/-- Restriction retains the same original target object function under codiscrete composition. -/
theorem homEquiv_target (C : Carrier.{u}) {O P : Type u} (F : C ⟶ object O) (g : O ⟶ P) :
    homEquiv C P (F ≫ functor.map g) = homEquiv C O F ≫ g := rfl

/-- The genuine original object-forgetting functor is left adjoint to codiscrete enrichment. -/
def adjunction : forgetObjects.{u} ⊣ functor.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun C O => (homEquiv C O).symm
      homEquiv_naturality_left_symm := by
        intro C D O F G
        exact homEquiv_source F O G
      homEquiv_naturality_right := by
        intro C O P f g
        apply (homEquiv C P).injective
        exact ((homEquiv_target C ((homEquiv C O).symm f) g).trans
          (congrArg (fun t => t ≫ g) ((homEquiv C O).apply_symm_apply f))).trans
            ((homEquiv C P).apply_symm_apply (f ≫ g)).symm }

/-- The actual codiscrete unit retains each individual original enriched object. -/
theorem unit_obj (C : Carrier.{u}) (x : C) : (adjunction.unit.app C).obj x = x := rfl

/-- The actual codiscrete counit retains each original label literally. -/
theorem counit_obj (O : Type u) (x : O) : adjunction.counit.app O x = x := rfl

/-- The entire object-forgetting triangle holds for the unchanged original enriched source. -/
theorem left_triangle (C : Carrier.{u}) :
    forgetObjects.map (adjunction.unit.app C) ≫ adjunction.counit.app (C : Type u) =
      𝟙 (C : Type u) :=
  adjunction.left_triangle_components C

/-- The whole codiscrete enriched triangle retains every original object and all unit Hom maps. -/
theorem right_triangle (O : Type u) :
    adjunction.unit.app (object O) ≫ functor.map (adjunction.counit.app O) = 𝟙 (object O) :=
  adjunction.right_triangle_components O

end CategoryTheory.SimplicialEnrichment.CodiscreteEnrichment
