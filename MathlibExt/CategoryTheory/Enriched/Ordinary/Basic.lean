/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Avocado
-/

module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment

@[expose] public section

universe v' v u u'
universe vV uV uA vA uB vB

open CategoryTheory Category MonoidalCategory Opposite

namespace CategoryTheory

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
  (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]

variable {X Y : C}

/-- The enriched identity `eId V Y` postcomposed with right whiskering by `f : X ⟶ Y`
recovers the enriched morphism `eHomEquiv V f`. -/
lemma eId_comp_eHomWhiskerRight (f : X ⟶ Y) :
    eId V Y ≫ eHomWhiskerRight V f Y = eHomEquiv V f := by
  dsimp [eHomWhiskerRight]
  calc eId V Y ≫ (λ_ (Y ⟶[V] Y)).inv ≫ eHomEquiv V f ▷ (Y ⟶[V] Y) ≫ eComp V X Y Y
      = (λ_ (𝟙_ V)).inv ≫ 𝟙_ V ◁ eId V Y ≫
          eHomEquiv V f ▷ (Y ⟶[V] Y) ≫ eComp V X Y Y := by
        rw [leftUnitor_inv_naturality_assoc]
    _ = (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ eId V Y) ≫ eComp V X Y Y := by
        rw [← MonoidalCategory.tensorHom_def'_assoc]
    _ = (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V f ⊗ₘ eHomEquiv V (𝟙 Y)) ≫ eComp V X Y Y := by
        rw [eHomEquiv_id]
    _ = eHomEquiv V (f ≫ 𝟙 Y) := by
        rw [← eHomEquiv_comp]
    _ = eHomEquiv V f := by
        rw [Category.comp_id]

/-- The enriched identity `eId V X` postcomposed with left whiskering by `f : X ⟶ Y`
recovers the enriched morphism `eHomEquiv V f`. -/
lemma eId_comp_eHomWhiskerLeft (f : X ⟶ Y) :
    eId V X ≫ eHomWhiskerLeft V X f = eHomEquiv V f := by
  dsimp [eHomWhiskerLeft]
  calc eId V X ≫ (ρ_ (X ⟶[V] X)).inv ≫ (X ⟶[V] X) ◁ eHomEquiv V f ≫ eComp V X X Y
      = (ρ_ (𝟙_ V)).inv ≫ eId V X ▷ 𝟙_ V ≫
          (X ⟶[V] X) ◁ eHomEquiv V f ≫ eComp V X X Y := by
        rw [rightUnitor_inv_naturality_assoc]
    _ = (λ_ (𝟙_ V)).inv ≫ eId V X ▷ 𝟙_ V ≫
          (X ⟶[V] X) ◁ eHomEquiv V f ≫ eComp V X X Y := by
        rw [← unitors_inv_equal]
    _ = (λ_ (𝟙_ V)).inv ≫ (eId V X ⊗ₘ eHomEquiv V f) ≫ eComp V X X Y := by
        rw [← MonoidalCategory.tensorHom_def_assoc]
    _ = (λ_ (𝟙_ V)).inv ≫ (eHomEquiv V (𝟙 X) ⊗ₘ eHomEquiv V f) ≫ eComp V X X Y := by
        rw [eHomEquiv_id]
    _ = eHomEquiv V (𝟙 X ≫ f) := by
        rw [← eHomEquiv_comp]
    _ = eHomEquiv V f := by
        rw [Category.id_comp]

/-- For `g : X' ⟶ X` and `f : X ⟶ Y`, postcomposing `eHomEquiv V f` with
right whiskering by `g` yields `eHomEquiv V (g ≫ f)`. -/
@[reassoc]
lemma eHomEquiv_comp_eHomWhiskerRight {X' X Y : C} (g : X' ⟶ X) (f : X ⟶ Y) :
    eHomEquiv V f ≫ eHomWhiskerRight V g Y = eHomEquiv V (g ≫ f) := by
  calc eHomEquiv V f ≫ eHomWhiskerRight V g Y
      = (eId V Y ≫ eHomWhiskerRight V f Y) ≫ eHomWhiskerRight V g Y := by
        rw [eId_comp_eHomWhiskerRight]
    _ = eId V Y ≫ (eHomWhiskerRight V f Y ≫ eHomWhiskerRight V g Y) := by
        rw [Category.assoc]
    _ = eId V Y ≫ eHomWhiskerRight V (g ≫ f) Y := by
        rw [← eHomWhiskerRight_comp]
    _ = eHomEquiv V (g ≫ f) := by
        rw [← eId_comp_eHomWhiskerRight]

/-- For `f : X ⟶ Y` and `g : Y ⟶ Y'`, postcomposing `eHomEquiv V f` with
left whiskering by `g` yields `eHomEquiv V (f ≫ g)`. -/
@[reassoc]
lemma eHomEquiv_comp_eHomWhiskerLeft {X Y Y' : C} (f : X ⟶ Y) (g : Y ⟶ Y') :
    eHomEquiv V f ≫ eHomWhiskerLeft V X g = eHomEquiv V (f ≫ g) := by
  calc eHomEquiv V f ≫ eHomWhiskerLeft V X g
      = (eId V X ≫ eHomWhiskerLeft V X f) ≫ eHomWhiskerLeft V X g := by
        rw [eId_comp_eHomWhiskerLeft]
    _ = eId V X ≫ (eHomWhiskerLeft V X f ≫ eHomWhiskerLeft V X g) := by
        rw [Category.assoc]
    _ = eId V X ≫ eHomWhiskerLeft V X (f ≫ g) := by
        rw [← eHomWhiskerLeft_comp]
    _ = eHomEquiv V (f ≫ g) := by
        rw [← eId_comp_eHomWhiskerLeft]

/-- Right enriched-hom whiskering respects a commutative square in the source. -/
@[reassoc]
theorem eHomWhiskerRight_commSq
    {W W' X X' Y : C} {T : V}
    (a : X' ⟶ X) (b : W' ⟶ X') (c : W ⟶ X) (d : W' ⟶ W)
    (h : b ≫ a = d ≫ c) (f : T ⟶ (X ⟶[V] Y)) :
    (f ≫ eHomWhiskerRight V a Y) ≫ eHomWhiskerRight V b Y =
      (f ≫ eHomWhiskerRight V c Y) ≫ eHomWhiskerRight V d Y := by
  calc
    (f ≫ eHomWhiskerRight V a Y) ≫ eHomWhiskerRight V b Y =
        f ≫ (eHomWhiskerRight V a Y ≫ eHomWhiskerRight V b Y) :=
      Category.assoc _ _ _
    _ = f ≫ eHomWhiskerRight V (b ≫ a) Y := by
      rw [eHomWhiskerRight_comp]
    _ = f ≫ eHomWhiskerRight V (d ≫ c) Y := by rw [h]
    _ = f ≫ (eHomWhiskerRight V c Y ≫ eHomWhiskerRight V d Y) := by
      rw [eHomWhiskerRight_comp]
    _ = (f ≫ eHomWhiskerRight V c Y) ≫ eHomWhiskerRight V d Y :=
      (Category.assoc _ _ _).symm

/-- Enriched-hom transport along a commutative source square, followed by a common output map. -/
@[reassoc]
theorem eHomWhisker_commSq
    {W W' X X' Y Y' : C} {T : V}
    (a : X' ⟶ X) (b : W' ⟶ X') (c : W ⟶ X) (d : W' ⟶ W)
    (h : b ≫ a = d ≫ c) (r : Y ⟶ Y')
    (f : T ⟶ (X ⟶[V] Y)) :
    ((f ≫ eHomWhiskerRight V a Y) ≫ eHomWhiskerLeft V X' r) ≫
        eHomWhiskerRight V b Y' =
      ((f ≫ eHomWhiskerRight V c Y) ≫ eHomWhiskerRight V d Y) ≫
        eHomWhiskerLeft V W' r := by
  rw [Category.assoc, eHom_whisker_exchange]
  simp only [Category.assoc]
  rw [← eHomWhiskerRight_comp_assoc V b a Y,
    ← eHomWhiskerRight_comp_assoc V d c Y, h]

/-- Right enriched-hom whiskering by an isomorphism is an isomorphism. -/
noncomputable def eHomWhiskerRightIso {X X' Y : C} (e : X ≅ X') :
    (X' ⟶[V] Y) ≅ (X ⟶[V] Y) where
  hom := eHomWhiskerRight V e.hom Y
  inv := eHomWhiskerRight V e.inv Y
  hom_inv_id := by
    have hcomp : eHomWhiskerRight V e.hom Y ≫ eHomWhiskerRight V e.inv Y =
        eHomWhiskerRight V (e.inv ≫ e.hom) Y :=
      (eHomWhiskerRight_comp V e.inv e.hom Y).symm
    have hIso : e.inv ≫ e.hom = 𝟙 X' := e.inv_hom_id
    have hSub := congrArg (eHomWhiskerRight V · Y) hIso
    have hId : eHomWhiskerRight V (𝟙 X') Y = 𝟙 (X' ⟶[V] Y) :=
      eHomWhiskerRight_id V X' Y
    exact hcomp.trans (hSub.trans hId)
  inv_hom_id := by
    have hcomp : eHomWhiskerRight V e.inv Y ≫ eHomWhiskerRight V e.hom Y =
        eHomWhiskerRight V (e.hom ≫ e.inv) Y :=
      (eHomWhiskerRight_comp V e.hom e.inv Y).symm
    have hIso : e.hom ≫ e.inv = 𝟙 X := e.hom_inv_id
    have hSub := congrArg (eHomWhiskerRight V · Y) hIso
    have hId : eHomWhiskerRight V (𝟙 X) Y = 𝟙 (X ⟶[V] Y) :=
      eHomWhiskerRight_id V X Y
    exact hcomp.trans (hSub.trans hId)

/-- Left enriched-hom whiskering by an isomorphism is an isomorphism. -/
noncomputable def eHomWhiskerLeftIso (X : C) {Y Y' : C} (e : Y ≅ Y') :
    (X ⟶[V] Y) ≅ (X ⟶[V] Y') where
  hom := eHomWhiskerLeft V X e.hom
  inv := eHomWhiskerLeft V X e.inv
  hom_inv_id := by
    have hcomp : eHomWhiskerLeft V X e.hom ≫ eHomWhiskerLeft V X e.inv =
        eHomWhiskerLeft V X (e.hom ≫ e.inv) :=
      (eHomWhiskerLeft_comp V X e.hom e.inv).symm
    have hIso : e.hom ≫ e.inv = 𝟙 Y := e.hom_inv_id
    have hSub := congrArg (eHomWhiskerLeft V X) hIso
    have hId : eHomWhiskerLeft V X (𝟙 Y) = 𝟙 (X ⟶[V] Y) :=
      eHomWhiskerLeft_id V X Y
    exact hcomp.trans (hSub.trans hId)
  inv_hom_id := by
    have hcomp : eHomWhiskerLeft V X e.inv ≫ eHomWhiskerLeft V X e.hom =
        eHomWhiskerLeft V X (e.inv ≫ e.hom) :=
      (eHomWhiskerLeft_comp V X e.inv e.hom).symm
    have hIso : e.inv ≫ e.hom = 𝟙 Y' := e.inv_hom_id
    have hSub := congrArg (eHomWhiskerLeft V X) hIso
    have hId : eHomWhiskerLeft V X (𝟙 Y') = 𝟙 (X ⟶[V] Y') :=
      eHomWhiskerLeft_id V X Y'
    exact hcomp.trans (hSub.trans hId)

/-- Right whiskering by an `IsIso` map yields an `IsIso` whisker. -/
theorem eHomWhiskerRight_isIso {X X' Y : C} (f : X ⟶ X') [IsIso f] :
    IsIso (eHomWhiskerRight V f Y) :=
  (eHomWhiskerRightIso V C (asIso f) (Y := Y)).isIso_hom

/-- Left whiskering by an `IsIso` map yields an `IsIso` whisker. -/
theorem eHomWhiskerLeft_isIso (X : C) {Y Y' : C} (g : Y ⟶ Y') [IsIso g] :
    IsIso (eHomWhiskerLeft V X g) :=
  (eHomWhiskerLeftIso V C X (asIso g)).isIso_hom

end CategoryTheory

namespace CategoryTheory
namespace EnrichedFunctor

section OrdinaryBridge

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
variable {A : Type uA} [Category.{vA} A] [EnrichedOrdinaryCategory V A]
variable {B : Type uB} [Category.{vB} B] [EnrichedOrdinaryCategory V B]

/-- The honest underlying functor of an enriched functor between enriched
ordinary categories, as the standard Mathlib composite: back along the
domain's `ForgetEnrichment.equiv`, through `EnrichedFunctor.forget`, then
forward along the codomain's `ForgetEnrichment.equivFunctor`. Functoriality
is inherited from the composite, so no identity or composition proofs are
needed here. The weight and diagram of
`EnrichedWeightedBar.IndexingData` descend to ordinary functors this way, so
ordinary coends apply to enriched-built integrands. -/
def toOrdinaryFunctor (F : EnrichedFunctor V A B) : A ⥤ B :=
  (ForgetEnrichment.equiv (D := A) V).inverse ⋙ F.forget ⋙
    ForgetEnrichment.equivFunctor V B

/-- The underlying functor agrees with the enriched functor on objects. -/
@[simp]
theorem toOrdinaryFunctor_obj (F : EnrichedFunctor V A B) (X : A) :
    F.toOrdinaryFunctor.obj X = F.obj X :=
  rfl

/-- The ordinary action of `toOrdinaryFunctor` in enriched terms. -/
theorem toOrdinaryFunctor_map (F : EnrichedFunctor V A B) {X Y : A}
    (f : X ⟶ Y) :
    eHomEquiv V (F.toOrdinaryFunctor.map f) = eHomEquiv V f ≫ F.map X Y := by
  have hmap : F.toOrdinaryFunctor.map f =
      (eHomEquiv V).symm (eHomEquiv V f ≫ F.map X Y) := rfl
  rw [hmap]
  exact Equiv.apply_symm_apply _ _

end OrdinaryBridge

section ClosedPointLaws

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [MonoidalClosed V]
variable {A : Type uA} [Category.{vA} A] [EnrichedOrdinaryCategory V A]

open scoped MonoidalClosed

/-- The uncurried enriched action of a `V`-valued enriched functor on a
tensor-unit point is the ordinary action up to the right unitor. -/
theorem uncurry_map_point (F : EnrichedFunctor V A V)
    {X Y : A} (f : X ⟶ Y) :
    (𝟙 (F.obj X) ⊗ₘ eHomEquiv V f) ≫
        MonoidalClosed.uncurry (F.map X Y) =
      (ρ_ (F.obj X)).hom ≫
        (F.toOrdinaryFunctor.map f : F.obj X ⟶ F.obj Y) := by
  rw [MonoidalClosed.uncurry_eq, ← Category.assoc, id_tensorHom,
    ← MonoidalCategory.whiskerLeft_comp, ← F.toOrdinaryFunctor_map,
    MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv]
  exact MonoidalClosed.whiskerLeft_curry'_ihom_ev_app _

end ClosedPointLaws

end EnrichedFunctor
end CategoryTheory
