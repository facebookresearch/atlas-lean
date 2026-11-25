/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.Restriction
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uA uB uC
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.RestrictionInversePair

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C]

private theorem component_eqToHom {X Y : EnrichedFunctorCat V A} (p : X = Y) (a : A) :
    component (eqToHom p) a =
      eqToHom (congrArg (fun X : EnrichedFunctorCat V A => X.toEnrichedFunctor.obj a) p) := by
  cases p
  rw [eqToHom_refl, component_id]
  rfl

private theorem restrictionMap_eqToHom (j : EnrichedFunctor V A B)
    {X Y : EnrichedFunctorCat V B} (p : X = Y) :
    restrictionMap j (eqToHom p) = eqToHom (congrArg (restrictionObject j) p) := by
  cases p
  simp only [eqToHom_refl]
  exact (restriction j).map_id X

private theorem compose_object (F : EnrichedFunctor V A B) (G : EnrichedFunctor V B C)
    (X : EnrichedFunctorCat V C) :
    (restriction G ⋙ restriction F).obj X = (restriction (F.comp V G)).obj X := by
  apply congrArg (fun H : EnrichedFunctor V A V => (⟨H⟩ : EnrichedFunctorCat V A))
  refine EnrichedFunctor.ext V (fun _ => rfl) ?_
  intro a b
  change (F.map a b ≫ G.map (F.obj a) (F.obj b) ≫
    X.toEnrichedFunctor.map (G.obj (F.obj a)) (G.obj (F.obj b))) ≫ eqToHom (by rfl) =
      (F.map a b ≫ G.map (F.obj a) (F.obj b)) ≫
        X.toEnrichedFunctor.map (G.obj (F.obj a)) (G.obj (F.obj b))
  rw [eqToHom_refl, Category.comp_id, Category.assoc]

/-- Both original restriction functors compose on every whole Hom action and transformation. -/
theorem restriction_comp (F : EnrichedFunctor V A B) (G : EnrichedFunctor V B C) :
    restriction G ⋙ restriction F = restriction (F.comp V G) := by
  refine Functor.ext (compose_object F G) ?_
  intro X Y t
  apply hom_ext
  intro a
  rw [component_comp, component_comp, component_eqToHom, component_eqToHom]
  change component (restrictionMap F (restrictionMap G t)) a = _
  rw [restrictionMap_component, restrictionMap_component, restrictionMap_component]
  change component t (G.obj (F.obj a)) =
    𝟙 (X.toEnrichedFunctor.obj (G.obj (F.obj a))) ≫
      component t (G.obj (F.obj a)) ≫ 𝟙 (Y.toEnrichedFunctor.obj (G.obj (F.obj a)))
  rw [Category.id_comp, Category.comp_id]

private theorem identity_object (X : EnrichedFunctorCat V A) :
    (restriction (EnrichedFunctor.id V A)).obj X = X := by
  apply congrArg (fun H : EnrichedFunctor V A V => (⟨H⟩ : EnrichedFunctorCat V A))
  refine EnrichedFunctor.ext V (fun _ => rfl) ?_
  intro a b
  change (𝟙 (a ⟶[V] b) ≫ X.toEnrichedFunctor.map a b) ≫ eqToHom (by rfl) =
    X.toEnrichedFunctor.map a b
  rw [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Actual identity restriction retains every full source action and original transformation. -/
theorem restriction_id : restriction (EnrichedFunctor.id V A) = 𝟭 (EnrichedFunctorCat V A) := by
  refine Functor.ext identity_object ?_
  intro X Y t
  apply hom_ext
  intro a
  rw [component_comp, component_comp, component_eqToHom, component_eqToHom,
    restrictionMap_component]
  change component t a = 𝟙 (X.toEnrichedFunctor.obj a) ≫
    component t a ≫ 𝟙 (Y.toEnrichedFunctor.obj a)
  rw [Category.id_comp, Category.comp_id]

variable (F : EnrichedFunctor V A B) (G : EnrichedFunctor V B A)
  (hFG : F.comp V G = EnrichedFunctor.id V A)
  (hGF : G.comp V F = EnrichedFunctor.id V B)

include hFG in
/-- Whole source diagrams and transformations are recovered from both entire index Hom maps. -/
theorem sourceRecovery : restriction G ⋙ restriction F = 𝟭 (EnrichedFunctorCat V A) := by
  rw [restriction_comp, hFG, restriction_id]

include hGF in
/-- Whole target diagrams and transformations are recovered from both actual inverse Hom maps. -/
theorem targetRecovery : restriction F ⋙ restriction G = 𝟭 (EnrichedFunctorCat V B) := by
  rw [restriction_comp, hGF, restriction_id]

/-- The original diagram unit is constructed from full source recovery. -/
@[no_expose]
def unitNatIso : 𝟭 (EnrichedFunctorCat V A) ≅ restriction G ⋙ restriction F :=
  eqToIso (sourceRecovery F G hFG).symm

/-- The original diagram counit is constructed from full target recovery. -/
@[no_expose]
def counitNatIso : restriction F ⋙ restriction G ≅ 𝟭 (EnrichedFunctorCat V B) :=
  eqToIso (targetRecovery F G hGF)

/-- Both actual diagram maps and the entire unit/counit satisfy the first triangle. -/
theorem source_triangle (X : EnrichedFunctorCat V A) :
    (restriction G).map ((unitNatIso F G hFG).hom.app X) ≫
      (counitNatIso F G hGF).hom.app ((restriction G).obj X) = 𝟙 _ := by
  unfold unitNatIso counitNatIso
  simp only [eqToIso.hom]
  rw [eqToHom_app, eqToHom_app, restrictionMap_eqToHom G,
    eqToHom_trans, eqToHom_refl]

/-- Both complete original diagram maps satisfy the other triangle. -/
theorem target_triangle (X : EnrichedFunctorCat V B) :
    (unitNatIso F G hFG).hom.app ((restriction F).obj X) ≫
      (restriction F).map ((counitNatIso F G hGF).hom.app X) = 𝟙 _ := by
  unfold unitNatIso counitNatIso
  simp only [eqToIso.hom]
  rw [eqToHom_app, eqToHom_app, restrictionMap_eqToHom F,
    eqToHom_trans, eqToHom_refl]

/-- The full enriched diagram carriers have actual inverse restrictions, unit and counit. -/
@[no_expose]
def diagramEquivalence : EnrichedFunctorCat V A ≌ EnrichedFunctorCat V B where
  functor := restriction G
  inverse := restriction F
  unitIso := unitNatIso F G hFG
  counitIso := counitNatIso F G hGF
  functor_unitIso_comp X := source_triangle F G hFG hGF X

private theorem unitNatIso_eq_proof : unitNatIso F G hFG =
    eqToIso (sourceRecovery F G hFG).symm := rfl

/-- The entire original diagram unit is the actual complete source-recovery equality. -/
theorem unitNatIso_eq : unitNatIso F G hFG =
    eqToIso (sourceRecovery F G hFG).symm := unitNatIso_eq_proof F G hFG

private theorem counitNatIso_eq_proof : counitNatIso F G hGF =
    eqToIso (targetRecovery F G hGF) := rfl

/-- The entire original counit is the actual complete target-recovery equality. -/
theorem counitNatIso_eq : counitNatIso F G hGF =
    eqToIso (targetRecovery F G hGF) := counitNatIso_eq_proof F G hGF

private theorem equivalence_functor_proof :
    (diagramEquivalence F G hFG hGF).functor = restriction G := rfl

/-- The whole forward carrier functor is the literal original enriched restriction. -/
theorem equivalence_functor :
    (diagramEquivalence F G hFG hGF).functor = restriction G :=
  equivalence_functor_proof F G hFG hGF

private theorem equivalence_inverse_proof :
    (diagramEquivalence F G hFG hGF).inverse = restriction F := rfl

/-- The whole inverse carrier functor is the actual complete inverse restriction. -/
theorem equivalence_inverse :
    (diagramEquivalence F G hFG hGF).inverse = restriction F :=
  equivalence_inverse_proof F G hFG hGF

private theorem equivalence_unit_proof :
    HEq (diagramEquivalence F G hFG hGF).unitIso (unitNatIso F G hFG) := by rfl

/-- The actual original natural unit is retained before taking any level component. -/
theorem equivalence_unit :
    HEq (diagramEquivalence F G hFG hGF).unitIso (unitNatIso F G hFG) :=
  equivalence_unit_proof F G hFG hGF

private theorem equivalence_counit_proof :
    HEq (diagramEquivalence F G hFG hGF).counitIso (counitNatIso F G hGF) := by rfl

/-- The actual original natural counit is retained as an entire natural isomorphism. -/
theorem equivalence_counit :
    HEq (diagramEquivalence F G hFG hGF).counitIso (counitNatIso F G hGF) :=
  equivalence_counit_proof F G hFG hGF

end CategoryTheory.EnrichedFunctorCat.RestrictionInversePair
