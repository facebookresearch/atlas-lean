/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Presentable.BoundedPresheafArrows
public import MathlibExt.AlgebraicTopology.SimplicialSpace.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# Bounded representatives of simplicial-space arrows

A property of simplicial-space arrows with uniformly bounded total point counts at both
endpoints has representatives indexed in the value universe. Each representative satisfies the
property and every arrow satisfying it is isomorphic to a representative; the property may be
arbitrary and need not be closed under isomorphism.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits

namespace SimplicialSpace

/-- A fiber injects into the literal total-point type at its original site object. -/
private theorem obj_cardinal_le_elements {C : Type} [Category.{v} C]
    (F : C ⥤ Type u) (X : C) : Cardinal.mk (F.obj X) ≤ Cardinal.mk F.Elements := by
  apply Cardinal.mk_le_of_injective (f := F.elementsMk X)
  intro x y h
  cases h
  rfl

/-- Every property of original simplicial-space arrows with bounded TOTAL
endpoint points has actual Type-u representatives belonging to that same property.
An arbitrary extra predicate is permitted; no isomorphism-closure hypothesis is needed. -/
theorem exists_bounded_arrow_representatives (γ : Cardinal.{u})
    (P : ObjectProperty (Arrow SimplicialSpace.{u}))
    (hP : ∀ a, P a →
      Cardinal.mk (Functor.uncurry.obj a.left.diagram).Elements ≤ γ ∧
      Cardinal.mk (Functor.uncurry.obj a.right.diagram).Elements ≤ γ) :
    ∃ (ι : Type u) (r : ι → Arrow SimplicialSpace.{u}),
      (∀ i, P (r i)) ∧ ∀ a, P a → ∃ i, Nonempty (a ≅ r i) := by
  let S := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ
  let _ : Small.{u} S := inferInstance
  let _ : LocallySmall.{u} S := inferInstance
  let e : SimplicialSpace.{u} ≌ (S ⥤ Type u) :=
    SimplicialSpace.equivalenceSimplicialObject.trans Functor.currying
  let E : Arrow SimplicialSpace.{u} ≌ Arrow (S ⥤ Type u) :=
    Functor.mapArrowEquivalence e
  let P' : ObjectProperty (Arrow (S ⥤ Type u)) := P.strictMap E.functor
  have hP' : ∀ a, P' a → ∀ X : S,
      Cardinal.mk (a.left.obj X) ≤ γ ∧ Cardinal.mk (a.right.obj X) ≤ γ := by
    intro a ha X
    obtain ⟨a₀, ha₀, rfl⟩ := (P.strictMap_iff E.functor a).1 ha
    obtain ⟨hL, hR⟩ := hP a₀ ha₀
    exact ⟨(obj_cardinal_le_elements (Functor.uncurry.obj a₀.left.diagram) X).trans hL,
      (obj_cardinal_le_elements (Functor.uncurry.obj a₀.right.diagram) X).trans hR⟩
  let _ : ObjectProperty.EssentiallySmall.{u} P' :=
    ObjectProperty.essentiallySmall_presheaf_arrows_of_pointwise_bound γ P' hP'
  let Q : ObjectProperty (Arrow SimplicialSpace.{u}) := P'.map E.inverse
  let _ : ObjectProperty.EssentiallySmall.{u} Q := inferInstance
  have hPQ : P ≤ Q := by
    intro a ha
    exact ⟨E.functor.obj a, P.strictMap_obj E.functor ha, ⟨(E.unitIso.app a).symm⟩⟩
  let _ : ObjectProperty.EssentiallySmall.{u} P :=
    ObjectProperty.EssentiallySmall.of_le hPQ
  obtain ⟨P₀, hsmall, hP₀, hcover⟩ := ObjectProperty.EssentiallySmall.exists_small_le.{u} P
  let _ : ObjectProperty.Small.{u} P₀ := hsmall
  obtain ⟨ι, r, hr⟩ := ObjectProperty.Small.exists_eq_ofObj.{u} P₀
  refine ⟨ι, r, ?_, ?_⟩
  · intro i
    apply hP₀
    rw [hr]
    exact ObjectProperty.ofObj_apply r i
  · intro a ha
    obtain ⟨b, hb, ⟨eb⟩⟩ := hcover a ha
    rw [hr] at hb
    obtain ⟨i, hi⟩ := (ObjectProperty.ofObj_iff r b).1 hb
    exact ⟨i, ⟨eb ≪≫ eqToIso hi.symm⟩⟩

end SimplicialSpace
