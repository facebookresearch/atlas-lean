/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.FunctorCategory

/-!
# Functor Category Iso

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uA
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

omit [BraidedCategory V] in
/-- The full inverse naturality square follows from actual component inverses and the forward
  square. -/
theorem inverse_components_naturality (F G : EnrichedFunctorCat V A)
    (e : ∀ X, F.toEnrichedFunctor.obj X ≅ G.toEnrichedFunctor.obj X)
    (h : ∀ X Y, MonoidalClosed.uncurry (F.toEnrichedFunctor.map X Y) ≫ (e Y).hom =
      ((e X).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map X Y))
    (X Y : A) :
    MonoidalClosed.uncurry (G.toEnrichedFunctor.map X Y) ≫ (e Y).inv =
      ((e X).inv ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map X Y) := by
  apply (cancel_mono (e Y).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h X Y, tensorHom_comp_tensorHom_assoc]
  simp only [Iso.inv_hom_id, Category.comp_id, id_tensorHom_id, Category.id_comp]

/-- Actual component isomorphisms with full Hom naturality give an isomorphism of genuine enriched
  functors. -/
def isoOfComponents (F G : EnrichedFunctorCat V A)
    (e : ∀ X, F.toEnrichedFunctor.obj X ≅ G.toEnrichedFunctor.obj X)
    (h : ∀ X Y, MonoidalClosed.uncurry (F.toEnrichedFunctor.map X Y) ≫ (e Y).hom =
      ((e X).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map X Y)) : F ≅ G
        where
  hom := GradedNatTrans.unitOfComponents (fun X => (e X).hom) h
  inv := GradedNatTrans.unitOfComponents (fun X => (e X).inv) (inverse_components_naturality F G e
    h)
  hom_inv_id := by
    apply EnrichedFunctorCat.hom_ext
    intro X
    change (eHomEquiv V).symm ((GradedNatTrans.unitComp _ _).app X) =
      (eHomEquiv V).symm ((GradedNatTrans.unitId F.toEnrichedFunctor).app X)
    rw [GradedNatTrans.unitComp_component, GradedNatTrans.unitOfComponents_component,
      GradedNatTrans.unitOfComponents_component, GradedNatTrans.unitId_component]
    exact (e X).hom_inv_id
  inv_hom_id := by
    apply EnrichedFunctorCat.hom_ext
    intro X
    change (eHomEquiv V).symm ((GradedNatTrans.unitComp _ _).app X) =
      (eHomEquiv V).symm ((GradedNatTrans.unitId G.toEnrichedFunctor).app X)
    rw [GradedNatTrans.unitComp_component, GradedNatTrans.unitOfComponents_component,
      GradedNatTrans.unitOfComponents_component, GradedNatTrans.unitId_component]
    exact (e X).inv_hom_id

/-- The forward map has the original supplied component. -/
@[simp]
theorem isoOfComponents_hom_component (F G : EnrichedFunctorCat V A)
    (e : ∀ X, F.toEnrichedFunctor.obj X ≅ G.toEnrichedFunctor.obj X)
    (h : ∀ X Y, MonoidalClosed.uncurry (F.toEnrichedFunctor.map X Y) ≫ (e Y).hom =
      ((e X).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map X Y)) (X : A) :
    EnrichedFunctorCat.component (isoOfComponents F G e h).hom X = (e X).hom :=
  GradedNatTrans.unitOfComponents_component (fun X => (e X).hom) h X

/-- The inverse component is the same original inverse. -/
@[simp]
theorem isoOfComponents_inv_component (F G : EnrichedFunctorCat V A)
    (e : ∀ X, F.toEnrichedFunctor.obj X ≅ G.toEnrichedFunctor.obj X)
    (h : ∀ X Y, MonoidalClosed.uncurry (F.toEnrichedFunctor.map X Y) ≫ (e Y).hom =
      ((e X).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫ MonoidalClosed.uncurry (G.toEnrichedFunctor.map X Y)) (X : A) :
    EnrichedFunctorCat.component (isoOfComponents F G e h).inv X = (e X).inv :=
  GradedNatTrans.unitOfComponents_component (fun X => (e X).inv)
    (inverse_components_naturality F G e h) X

end CategoryTheory.EnrichedFunctorCat
