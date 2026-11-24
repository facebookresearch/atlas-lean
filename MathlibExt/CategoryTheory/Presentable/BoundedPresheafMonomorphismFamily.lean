/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.MorphismProperty.BoundedPresheafMonomorphisms
public import MathlibExt.CategoryTheory.Presentable.BoundedPresheafArrows
public import MathlibExt.CategoryTheory.Presentable.SmallFunctorCategory
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.SmallObject.Basic

/-!
# Literal bounded monomorphism representatives

The family is selected inside the property of original bounded monomorphisms through its
native small model. Both endpoint ranks and every small-object-argument field are derived
before invoking the native factorization at the same regular cardinal.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

namespace CategoryTheory.Presheaf

variable (E : Type u) [SmallCategory E]

/-- The property of original bounded monomorphisms is essentially small in the value universe. -/
theorem boundedMonoArrows_essentiallySmall :
    ObjectProperty.EssentiallySmall.{u} (boundedMonoArrows E) := by
  apply ObjectProperty.essentiallySmall_presheaf_arrows_of_pointwise_bound
    (max Cardinal.aleph0 (Cardinal.mk (Arrow E))) (boundedMonoArrows E)
  intro a ha e
  have hL : Cardinal.mk (a.left.obj e) ≤ Cardinal.mk a.left.Elements :=
    Cardinal.mk_le_of_injective (f := fun x : a.left.obj e => a.left.elementsMk e x)
      (fun x y h => by cases h; rfl)
  have hR : Cardinal.mk (a.right.obj e) ≤ Cardinal.mk a.right.Elements :=
    Cardinal.mk_le_of_injective (f := fun x : a.right.obj e => a.right.elementsMk e x)
      (fun x y h => by cases h; rfl)
  exact ⟨hL.trans ha.2.1, hR.trans ha.2.2⟩

/-- Select representatives inside any original subproperty of bounded monomorphisms,
including the empty property, and derive both endpoint ranks and native eligibility. -/
theorem exists_bounded_mono_family_of_property
    (P : ObjectProperty (Arrow (Eᵒᵖ ⥤ Type u))) (hP : P ≤ boundedMonoArrows E) :
    ∃ (K : Type u) (F : K → Arrow (Eᵒᵖ ⥤ Type u))
      (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      max Cardinal.aleph0 (Cardinal.mk (Arrow E)) < κ ∧
        (∀ k, P (F k)) ∧
        (∀ a, P a → ∃ k, Nonempty (a ≅ F k)) ∧
        (∀ k, IsCardinalPresentable (F k).left κ ∧ IsCardinalPresentable (F k).right κ) ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).IsSmall.{u} ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).IsCardinalForSmallObjectArgument κ ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).HasSmallObjectArgument.{u} ∧
        Nonempty (MorphismProperty.FunctorialFactorizationData
          (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp.llp
          (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp) := by
  let C := Eᵒᵖ ⥤ Type u
  let _ : ObjectProperty.EssentiallySmall.{u} (boundedMonoArrows E) :=
    boundedMonoArrows_essentiallySmall E
  let _ : ObjectProperty.EssentiallySmall.{u} P := ObjectProperty.EssentiallySmall.of_le hP
  let V := P.FullSubcategory
  let _ : EssentiallySmall.{u} V := inferInstance
  let K : Type u := SmallModel.{u} V
  let e : V ≌ K := equivSmallModel.{u} V
  let F : K → Arrow C := fun k => P.ι.obj (e.inverse.obj k)
  have hF (k : K) : P (F k) := (e.inverse.obj k).property
  have hcover (a : Arrow C) (ha : P a) :
      ∃ k : K, Nonempty (a ≅ F k) :=
    ⟨e.functor.obj ⟨a, ha⟩, ⟨P.ι.mapIso (e.unitIso.app ⟨a, ha⟩)⟩⟩
  let _ : IsLocallyPresentable.{u} C :=
    isLocallyPresentable_presheaf_of_essentiallySmall E (Type u)
  let endpoints : K × Bool → C := fun s => if s.2 then (F s.1).right else (F s.1).left
  let Q : ObjectProperty C := ObjectProperty.ofObj endpoints
  let _ : ObjectProperty.Small.{u} Q := inferInstance
  let _ : ObjectProperty.EssentiallySmall.{u} Q := inferInstance
  obtain ⟨μ, hμ, hQ⟩ := ObjectProperty.le_isCardinalPresentable Q
  let _ : Fact μ.IsRegular := hμ
  let θ : Cardinal.{u} := max Cardinal.aleph0 (Cardinal.mk (Arrow E))
  let Upper := μ.ord.ToType ⊕ θ.ord.ToType
  obtain ⟨κ, hk, hUpper⟩ := HasCardinalLT.exists_regular_cardinal.{u} Upper
  let _ : Fact κ.IsRegular := ⟨hk⟩
  have hμκ : μ < κ := by
    have h := hUpper.of_injective (Sum.inl : μ.ord.ToType → Upper) Sum.inl_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hθκ : θ < κ := by
    have h := hUpper.of_injective (Sum.inr : θ.ord.ToType → Upper) Sum.inr_injective
    simpa only [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_ord_toType] using h
  have hends (k : K) :
      IsCardinalPresentable (F k).left κ ∧ IsCardinalPresentable (F k).right κ := by
    have hL : IsCardinalPresentable (F k).left μ :=
      hQ _ (ObjectProperty.ofObj_apply endpoints (k, false))
    have hR : IsCardinalPresentable (F k).right μ :=
      hQ _ (ObjectProperty.ofObj_apply endpoints (k, true))
    let _ := hL
    let _ := hR
    exact ⟨isCardinalPresentable_of_le (F k).left hμκ.le,
      isCardinalPresentable_of_le (F k).right hμκ.le⟩
  have : Nonempty κ.ord.ToType := by simpa using hk.ne_zero
  let _ : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  let M : MorphismProperty C := MorphismProperty.ofHoms (fun k => (F k).hom)
  let _ : M.IsSmall.{u} := inferInstance
  have heligible : M.IsCardinalForSmallObjectArgument κ :=
    { isSmall := inferInstance
      locallySmall := inferInstance
      hasPushouts := inferInstance
      hasCoproducts := inferInstance
      hasIterationOfShape := inferInstance
      preservesColimit := by
        intro A B X Y i hi p c
        change MorphismProperty.ofHoms (fun k => (F k).hom) i at hi
        cases hi with
        | mk k =>
          let _ : IsCardinalPresentable (F k).left κ := (hends k).1
          let _ : PreservesColimitsOfShape κ.ord.ToType (coyoneda.obj (op (F k).left)) :=
            preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall
              (F k).left κ κ.ord.ToType
          infer_instance }
  let _ := heligible
  have hsoa : M.HasSmallObjectArgument.{u} := ⟨κ, inferInstance, inferInstance, heligible⟩
  exact ⟨K, F, κ, inferInstance, inferInstance, hθκ, hF, hcover, hends,
    inferInstance, heligible, hsoa, ⟨SmallObject.functorialFactorizationData M κ⟩⟩

/-- The full original bounded-monomorphism property has a literal small family of
members, whole Arrow coverage, both absolute endpoint ranks and native SOA at one
internally produced regular cardinal. -/
theorem exists_bounded_mono_family :
    ∃ (K : Type u) (F : K → Arrow (Eᵒᵖ ⥤ Type u))
      (κ : Cardinal.{u}) (hκ : Fact κ.IsRegular) (hbot : OrderBot κ.ord.ToType),
      letI : Fact κ.IsRegular := hκ
      letI : OrderBot κ.ord.ToType := hbot
      max Cardinal.aleph0 (Cardinal.mk (Arrow E)) < κ ∧
        (∀ k, boundedMonoArrows E (F k)) ∧
        (∀ a, boundedMonoArrows E a → ∃ k, Nonempty (a ≅ F k)) ∧
        (∀ k, IsCardinalPresentable (F k).left κ ∧ IsCardinalPresentable (F k).right κ) ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).IsSmall.{u} ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).IsCardinalForSmallObjectArgument κ ∧
        (MorphismProperty.ofHoms (fun k => (F k).hom)).HasSmallObjectArgument.{u} ∧
        Nonempty (MorphismProperty.FunctorialFactorizationData
          (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp.llp
          (MorphismProperty.ofHoms (fun k => (F k).hom)).rlp) :=
  exists_bounded_mono_family_of_property E (boundedMonoArrows E) le_rfl

end CategoryTheory.Presheaf
