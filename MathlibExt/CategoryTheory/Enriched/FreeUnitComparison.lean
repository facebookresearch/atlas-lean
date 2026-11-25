/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.ScalarFreeTensor

/-!
# The actual unit coefficient of a free enriched diagram

The full free diagram on the tensor unit is the original covariant
representable with its actual scalar unitor.  Both complete morphisms,
source naturalities, and identity evaluation retain the supplied enrichment.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uV vV uI

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.Free

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]

private theorem component_eqToIso_hom {F G : EnrichedFunctorCat V I}
    (h : F = G) (i : I) :
    component (eqToIso h).hom i =
      eqToHom (congrArg (fun X : EnrichedFunctorCat V I =>
        X.toEnrichedFunctor.obj i) h) := by
  cases h
  exact component_id F i

private theorem component_eqToIso_inv {F G : EnrichedFunctorCat V I}
    (h : F = G) (i : I) :
    component (eqToIso h).inv i =
      eqToHom (congrArg (fun X : EnrichedFunctorCat V I =>
        X.toEnrichedFunctor.obj i) h.symm) := by
  cases h
  exact component_id F i

/-- The whole original free diagram on the actual tensor unit is representable. -/
@[no_expose]
def unitCoefficientIso (a : I) :
    object a (𝟙_ V) ≅ representableObject a :=
  eqToIso (object_eq_scalarRepresentable a (𝟙_ V)) ≪≫
    scalarUnitIso (representableObject a)

/-- Every full forward component is the original ambient left unitor. -/
theorem unitCoefficientIso_hom_component (a i : I) :
    component (unitCoefficientIso (V := V) a).hom i =
      (λ_ (a ⟶[V] i)).hom := by
  unfold unitCoefficientIso
  rw [Iso.trans_hom, component_comp, component_eqToIso_hom,
    scalarUnitIso_hom_component]
  change 𝟙 ((𝟙_ V) ⊗ (a ⟶[V] i)) ≫ (λ_ (a ⟶[V] i)).hom = _
  exact Category.id_comp _

/-- Every full inverse component is the inverse of that same original unitor. -/
theorem unitCoefficientIso_inv_component (a i : I) :
    component (unitCoefficientIso (V := V) a).inv i =
      (λ_ (a ⟶[V] i)).inv := by
  unfold unitCoefficientIso
  rw [Iso.trans_inv, component_comp, scalarUnitIso_inv_component,
    component_eqToIso_inv]
  change (λ_ (a ⟶[V] i)).inv ≫ 𝟙 ((𝟙_ V) ⊗ (a ⟶[V] i)) = _
  exact Category.comp_id _

/-- Forward naturality retains the entire original enriched Hom object. -/
theorem unitCoefficientIso_hom_fullHom (a i j : I) :
    MonoidalClosed.uncurry ((object a (𝟙_ V)).toEnrichedFunctor.map i j) ≫
        (λ_ (a ⟶[V] j)).hom =
      ((λ_ (a ⟶[V] i)).hom ⊗ₘ 𝟙 (i ⟶[V] j)) ≫
        eComp V a i j := by
  have h := (unitCoefficientIso (V := V) a).hom.uncurriedNaturality i j
  change MonoidalClosed.uncurry ((object a (𝟙_ V)).toEnrichedFunctor.map i j) ≫
      component (unitCoefficientIso a).hom j =
    (component (unitCoefficientIso a).hom i ⊗ₘ 𝟙 (i ⟶[V] j)) ≫
      MonoidalClosed.uncurry ((representableObject a).toEnrichedFunctor.map i j) at h
  rw [unitCoefficientIso_hom_component, unitCoefficientIso_hom_component,
    GradedYoneda.representable_uncurry] at h
  exact h

/-- Inverse naturality retains the same complete source and target Hom objects. -/
theorem unitCoefficientIso_inv_fullHom (a i j : I) :
    eComp V a i j ≫ (λ_ (a ⟶[V] j)).inv =
      ((λ_ (a ⟶[V] i)).inv ⊗ₘ 𝟙 (i ⟶[V] j)) ≫
        MonoidalClosed.uncurry ((object a (𝟙_ V)).toEnrichedFunctor.map i j) := by
  have h := (unitCoefficientIso (V := V) a).inv.uncurriedNaturality i j
  change MonoidalClosed.uncurry ((representableObject a).toEnrichedFunctor.map i j) ≫
      component (unitCoefficientIso a).inv j =
    (component (unitCoefficientIso a).inv i ⊗ₘ 𝟙 (i ⟶[V] j)) ≫
      MonoidalClosed.uncurry ((object a (𝟙_ V)).toEnrichedFunctor.map i j) at h
  rw [unitCoefficientIso_inv_component, unitCoefficientIso_inv_component,
    GradedYoneda.representable_uncurry] at h
  exact h

/-- Identity evaluation of the complete forward map is the original enriched identity. -/
theorem unitCoefficientIso_identity_evaluation (a : I) :
    evaluate a (𝟙_ V) (representableObject a) (unitCoefficientIso a).hom =
      eId V a := by
  rw [evaluate, unitCoefficientIso_hom_component]
  have h := leftUnitor_naturality (eId V a)
  change (ρ_ (𝟙_ V)).inv ≫
      ((𝟙_ V) ◁ eId V a) ≫ (λ_ (a ⟶[V] a)).hom = eId V a
  rw [h, ← unitors_inv_equal, Iso.inv_hom_id_assoc]

/-- The whole original source-map function retains its full Hom precomposition. -/
theorem unitCoefficientIso_source_hom {a a' : I}
    (e : 𝟙_ V ⟶ (a ⟶[V] a')) (i : I) :
    component (sourceMap e (𝟙_ V)) i ≫
        component (unitCoefficientIso a).hom i =
      component (unitCoefficientIso a').hom i ≫ sourceHomMap e i := by
  rw [sourceMap_component, unitCoefficientIso_hom_component,
    unitCoefficientIso_hom_component]
  exact leftUnitor_naturality (sourceHomMap e i)

/-- The inverse complete component preserves the original source-map function. -/
theorem unitCoefficientIso_source_inv {a a' : I}
    (e : 𝟙_ V ⟶ (a ⟶[V] a')) (i : I) :
    sourceHomMap e i ≫ component (unitCoefficientIso a).inv i =
      component (unitCoefficientIso a').inv i ≫
        component (sourceMap e (𝟙_ V)) i := by
  rw [sourceMap_component, unitCoefficientIso_inv_component,
    unitCoefficientIso_inv_component]
  exact leftUnitor_inv_naturality (sourceHomMap e i)

end CategoryTheory.EnrichedFunctorCat.Free
