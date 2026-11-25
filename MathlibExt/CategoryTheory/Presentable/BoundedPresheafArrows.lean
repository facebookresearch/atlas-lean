/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Comma.Arrow

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ObjectProperty

variable {C : Type uC} [Category.{vC} C]

/-- Lift the whole original arrow, including every original natural component. -/
private def valueLiftArrow (V : ObjectProperty (Type u))
    (a : Arrow (C ⥤ Type u))
    (hL : ∀ X, V (a.left.obj X)) (hR : ∀ X, V (a.right.obj X)) :
    Arrow (C ⥤ V.FullSubcategory) :=
  Arrow.mk (show V.lift a.left hL ⟶ V.lift a.right hR from
    { app X := ObjectProperty.homMk (a.hom.app X)
      naturality X Y f := by
        apply ObjectProperty.hom_ext
        change a.left.map f ≫ a.hom.app Y = a.hom.app X ≫ a.right.map f
        exact a.hom.naturality f })

/-- Forgetting the lift retains both original endpoints and the whole natural arrow. -/
private theorem valueLiftArrow_map_eq (V : ObjectProperty (Type u))
    (a : Arrow (C ⥤ Type u))
    (hL : ∀ X, V (a.left.obj X)) (hR : ∀ X, V (a.right.obj X)) :
    ((Functor.whiskeringRight C V.FullSubcategory (Type u)).obj V.ι).mapArrow.obj
      (valueLiftArrow V a hL hR) = a := by
  cases a
  rfl

/-- A working-universe-small site and bounded values give essential smallness
of the actual arrow property. No whole-presheaf presentability is assumed. -/
theorem essentiallySmall_presheaf_arrows_of_pointwise_bound
    [Small.{u} C] [LocallySmall.{u} C] (γ : Cardinal.{u})
    (P : ObjectProperty (Arrow (C ⥤ Type u)))
    (hP : ∀ a, P a → ∀ X : C,
      Cardinal.mk (a.left.obj X) ≤ γ ∧ Cardinal.mk (a.right.obj X) ≤ γ) :
    ObjectProperty.EssentiallySmall.{u} P := by
  obtain ⟨κ, hκ, hΓ⟩ := HasCardinalLT.exists_regular_cardinal.{u} γ.out
  let _ : Fact κ.IsRegular := ⟨hκ⟩
  have hγκ : γ < κ := by
    have h := (hasCardinalLT_iff_cardinal_mk_lt γ.out κ).1 hΓ
    simpa only [Cardinal.mk_out] using h
  let V : ObjectProperty (Type u) := isCardinalPresentable (Type u) κ
  let _ : IsCardinalLocallyPresentable (Type u) κ := inferInstance
  let _ : ObjectProperty.EssentiallySmall.{u} V := by
    dsimp [V]
    infer_instance
  let A := V.FullSubcategory
  let _ : Category.{u} A := inferInstance
  let _ : EssentiallySmall.{u} A := inferInstance
  let K : Type u := SmallModel.{u} A
  let _ : SmallCategory K := inferInstance
  let e : A ≌ K := equivSmallModel.{u} A
  let E : (C ⥤ A) ≌ (C ⥤ K) := Equivalence.congrRight e
  let L : (C ⥤ A) ⥤ (C ⥤ Type u) :=
    (Functor.whiskeringRight C A (Type u)).obj V.ι
  let _ : Small.{u} (C ⥤ K) := inferInstance
  let _ : LocallySmall.{u} (C ⥤ K) :=
    { hom_small F G := small_of_injective
        (f := fun η : F ⟶ G => η.app) (fun f g h => NatTrans.ext h) }
  let _ : Small.{u} (Arrow (C ⥤ K)) := inferInstance
  let R : Arrow (C ⥤ K) → Arrow (C ⥤ Type u) :=
    fun a => (E.inverse ⋙ L).mapArrow.obj a
  refine ⟨⟨ObjectProperty.ofObj R, inferInstance, ?_⟩⟩
  intro a ha
  have hL : ∀ X, V (a.left.obj X) := by
    intro X
    change IsCardinalPresentable (a.left.obj X) κ
    exact ((hasCardinalLT_iff_cardinal_mk_lt _ _).2
      ((hP a ha X).1.trans_lt hγκ)).isCardinalPresentable
  have hR : ∀ X, V (a.right.obj X) := by
    intro X
    change IsCardinalPresentable (a.right.obj X) κ
    exact ((hasCardinalLT_iff_cardinal_mk_lt _ _).2
      ((hP a ha X).2.trans_lt hγκ)).isCardinalPresentable
  let aV : Arrow (C ⥤ A) := valueLiftArrow V a hL hR
  let b : Arrow (C ⥤ K) := E.functor.mapArrow.obj aV
  have h0 : L.mapArrow.obj aV = a := valueLiftArrow_map_eq V a hL hR
  let eV : aV ≅ E.inverse.mapArrow.obj b :=
    (Functor.mapArrowEquivalence E).unitIso.app aV
  let eD : L.mapArrow.obj aV ≅ R b := L.mapArrow.mapIso eV
  exact ⟨R b, ObjectProperty.ofObj_apply R b, ⟨eqToIso h0.symm ≪≫ eD⟩⟩

end CategoryTheory.ObjectProperty
