/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.HomPowerAccessibility
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Entire original Hom-power and compatible-rank contracts

The original five universes are independent. Whole Hom functions, both
index-label directions, actual unit/counit values and filtered-colimit
preservation are checked on the native selected functors. Concrete cases
include empty, infinite discrete, infinite nonthin and independently raised
Hom universes, plus a coefficient collapse and a nonidentity index Iso.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uM vM uD vD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Presentable.HomPowerAccessibilityTest

open HomPowerAccessibility

variable (M : Type uM) [Category.{vM} M] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalLocallyPresentable M κ]
  {D : Type uD} [Category.{vD} D] {S : Type w} [SmallCategory S] (s : D ≌ S)

example : HasPullbacks M := hasPullbacks M κ

example : IsCardinalLocallyPresentable (D ⥤ M) κ := diagramLocallyPresentable M κ s

example (d : D) : Functor.IsAccessible.{w} (Completeness.cofree M κ s d) :=
  cofree_isAccessible M κ s d

example (d e : D) : Functor.IsAccessible.{w} (Completeness.homPower M κ s d e) :=
  homPower_isAccessible M κ s d e

example (d : D) : PreservesColimitsOfSize.{w, w} ((evaluation D M).obj d) :=
  evaluation_preservesColimits M κ d

example {F G : D ⥤ M} (a : F ⟶ G) (d : D) :
    ((evaluation D M).obj d).map a = a.app d := rfl

example (d e : D) :
    Completeness.homPower M κ s d e =
      Completeness.cofree M κ s d ⋙ (evaluation D M).obj e := rfl

example (e : D) :
    let _ (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
    free M κ s e = evaluationLeftAdjoint M e := rfl

example (e : D) :
    let _ (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
    freeEvaluationAdjunction M κ s e = evaluationAdjunctionRight M e := rfl

example (d : D) :
    let _ (a b : D) : HasProductsOfShape (a ⟶ b) M := Completeness.homProducts M κ s a b
    Completeness.cofree M κ s d = evaluationRightAdjoint M d := rfl

example (d e : D) : homCopower M κ s d e = free M κ s e ⋙ (evaluation D M).obj d := rfl

example (d e : D) (X : M) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    (homCopower M κ s d e).obj X = ∐ fun _ : e ⟶ d ↦ X :=
  homCopower_obj M κ s d e X

example (d e : D) {X Y : M} (a : X ⟶ Y) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    (homCopower M κ s d e).map a =
      Sigma.desc (fun h : e ⟶ d ↦ a ≫ Sigma.ι (fun _ : e ⟶ d ↦ Y) h) :=
  homCopower_map M κ s d e a

example (d e : D) {X Y : M} (a : X ⟶ Y) :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    (Completeness.homPower M κ s d e).map a =
      Pi.lift (fun h : e ⟶ d ↦ Pi.π (fun _ : e ⟶ d ↦ X) h ≫ a) :=
  Completeness.homPower_map M κ s d e a

example (e : D) {d d' : D} (a : d ⟶ d') (X : M) (h : e ⟶ d) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    let _ : HasCoproductsOfShape (e ⟶ d') M := homCoproducts M κ s e d'
    Sigma.ι (fun _ : e ⟶ d ↦ X) h ≫ ((free M κ s e).obj X).map a =
      Sigma.ι (fun _ : e ⟶ d' ↦ X) (h ≫ a) :=
  free_index_map_ι M κ s e a X h

section WholeTransposeFunctions

example (e : D) (X : M) (F : D ⥤ M) :
    let _ : HasCoproductsOfShape (e ⟶ e) M := homCoproducts M κ s e e
    ((freeEvaluationAdjunction M κ s e).homEquiv X F :
      ((free M κ s e).obj X ⟶ F) → (X ⟶ F.obj e)) =
      fun a ↦ Sigma.ι (fun _ : e ⟶ e ↦ X) (𝟙 e) ≫ a.app e := by
  funext a
  exact free_homEquiv M κ s e X F a

example (e d : D) (X : M) (F : D ⥤ M) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    (fun a : X ⟶ F.obj e ↦
      (((freeEvaluationAdjunction M κ s e).homEquiv X F).symm a).app d) =
      fun a ↦ Sigma.desc (fun h : e ⟶ d ↦ a ≫ F.map h) := by
  funext a
  exact free_homEquiv_symm_app M κ s e d X F a

example (d e : D) (F : D ⥤ M) (Y : M) :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    (fun a : F.obj d ⟶ Y ↦
      (((Completeness.evaluationCofreeAdjunction M κ s d).homEquiv F Y) a).app e) =
      fun a ↦ Pi.lift (fun h : e ⟶ d ↦ F.map h ≫ a) := by
  funext a
  exact Completeness.cofree_homEquiv_app M κ s d e F Y a

example (d : D) (F : D ⥤ M) (Y : M) :
    let _ : HasProductsOfShape (d ⟶ d) M := Completeness.homProducts M κ s d d
    (((Completeness.evaluationCofreeAdjunction M κ s d).homEquiv F Y).symm :
      (F ⟶ (Completeness.cofree M κ s d).obj Y) → (F.obj d ⟶ Y)) =
      fun a ↦ a.app d ≫ Pi.π (fun _ : d ⟶ d ↦ Y) (𝟙 d) := by
  funext a
  exact Completeness.cofree_homEquiv_symm M κ s d F Y a

example (d e : D) (X Y : M) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    ((homCopowerPowerAdjunction M κ s d e).homEquiv X Y :
      ((homCopower M κ s d e).obj X ⟶ Y) →
        (X ⟶ (Completeness.homPower M κ s d e).obj Y)) =
      fun f ↦ Pi.lift (fun h : e ⟶ d ↦ Sigma.ι (fun _ : e ⟶ d ↦ X) h ≫ f) := by
  funext f
  exact homCopowerPower_homEquiv_apply M κ s d e f

example (d e : D) (X Y : M) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    (((homCopowerPowerAdjunction M κ s d e).homEquiv X Y).symm :
      (X ⟶ (Completeness.homPower M κ s d e).obj Y) →
        ((homCopower M κ s d e).obj X ⟶ Y)) =
      fun f ↦ Sigma.desc (fun h : e ⟶ d ↦ f ≫ Pi.π (fun _ : e ⟶ d ↦ Y) h) := by
  funext f
  exact homCopowerPower_homEquiv_symm_apply M κ s d e f

example (d e : D) (X : M) (h : e ⟶ d) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    (homCopowerPowerAdjunction M κ s d e).unit.app X ≫
        Pi.π (fun _ : e ⟶ d ↦ (homCopower M κ s d e).obj X) h =
      Sigma.ι (fun _ : e ⟶ d ↦ X) h :=
  homCopowerPower_unit_π M κ s d e X h

example (d e : D) (Y : M) (h : e ⟶ d) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    Sigma.ι (fun _ : e ⟶ d ↦ (Completeness.homPower M κ s d e).obj Y) h ≫
        (homCopowerPowerAdjunction M κ s d e).counit.app Y =
      Pi.π (fun _ : e ⟶ d ↦ Y) h :=
  homCopowerPower_counit_ι M κ s d e Y h

end WholeTransposeFunctions

section ActualIndexIsomorphisms

variable {d d' : D} (i : d ≅ d')

example (e : D) : (homLabelEquiv i e : (e ⟶ d) → (e ⟶ d')) =
    fun h ↦ h ≫ i.hom := by
  funext h
  exact homLabelEquiv_apply i e h

example (e : D) : ((homLabelEquiv i e).symm : (e ⟶ d') → (e ⟶ d)) =
    fun h ↦ h ≫ i.inv := by
  funext h
  exact homLabelEquiv_symm_apply i e h

example (X : M) (e : D) (h : e ⟶ d') :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d') M := Completeness.homProducts M κ s e d'
    (componentIso M κ s i X e).hom ≫ Pi.π (fun _ : e ⟶ d' ↦ X) h =
      Pi.π (fun _ : e ⟶ d ↦ X) (h ≫ i.inv) :=
  componentIso_hom_π M κ s i X e h

example (X : M) (e : D) (h : e ⟶ d) :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d') M := Completeness.homProducts M κ s e d'
    (componentIso M κ s i X e).inv ≫ Pi.π (fun _ : e ⟶ d ↦ X) h =
      Pi.π (fun _ : e ⟶ d' ↦ X) (h ≫ i.hom) :=
  componentIso_inv_π M κ s i X e h

example (X : M) {e f : D} (a : e ⟶ f) :
    ((Completeness.cofree M κ s d).obj X).map a ≫ (componentIso M κ s i X f).hom =
      (componentIso M κ s i X e).hom ≫ ((Completeness.cofree M κ s d').obj X).map a :=
  componentIso_naturality M κ s i X a

example {X Y : M} (a : X ⟶ Y) (e : D) :
    ((Completeness.cofree M κ s d).map a).app e ≫ (componentIso M κ s i Y e).hom =
      (componentIso M κ s i X e).hom ≫ ((Completeness.cofree M κ s d').map a).app e :=
  componentIso_coefficient_naturality M κ s i a e

example (X : M) (e : D) :
    ((cofreeIso M κ s i).hom.app X).app e = (componentIso M κ s i X e).hom :=
  cofreeIso_hom_app M κ s i X e

example (X : M) (e : D) :
    ((cofreeIso M κ s i).inv.app X).app e = (componentIso M κ s i X e).inv :=
  cofreeIso_inv_app M κ s i X e

example (F : D ⥤ M) :
    ((evaluation D M).mapIso i).hom.app F = F.map i.hom := rfl

example (F : D ⥤ M) :
    ((evaluation D M).mapIso i).inv.app F = F.map i.inv := rfl

example (d : D) : representativeIso M κ s d =
    cofreeIso M κ s (s.unitIso.app d) := rfl

end ActualIndexIsomorphisms

section ActualRanks

example (d e : D) (μ : Cardinal.{w}) [Fact μ.IsRegular]
    (h : HasCardinalLT (e ⟶ d) μ) (X : M) [IsCardinalPresentable X μ] :
    IsCardinalPresentable ((homCopower M κ s d e).obj X) μ :=
  homCopower_presentable M κ s d e μ h X

example (d e : D) (μ : Cardinal.{w}) [Fact μ.IsRegular]
    (hκ : κ ≤ μ) (h : HasCardinalLT (e ⟶ d) μ) :
    (Completeness.homPower M κ s d e).IsCardinalAccessible μ :=
  homPower_isCardinalAccessible_of_hom_bound M κ s d e μ hκ h

example (d e : D) (h : HasCardinalLT (e ⟶ d) κ) :
    (Completeness.homPower M κ s d e).IsCardinalAccessible κ :=
  homPower_isCardinalAccessible_fixed M κ s d e h

example (d : D) (μ : Cardinal.{w}) [Fact μ.IsRegular] (hκ : κ ≤ μ)
    (h : ∀ e : D, HasCardinalLT (e ⟶ d) μ) :
    (Completeness.cofree M κ s d).IsCardinalAccessible μ :=
  cofree_isCardinalAccessible_of_hom_bounds M κ s d μ hκ h

example (μ : Cardinal.{w}) (h : HasCardinalLT (Arrow S) μ) (d e : D) :
    HasCardinalLT (e ⟶ d) μ :=
  hom_bound_of_representative_arrows s μ h d e

example (h : HasCardinalLT (Arrow S) κ) :
    (∀ d : D, (Completeness.cofree M κ s d).IsCardinalAccessible κ) ∧
      ∀ d e : D, (Completeness.homPower M κ s d e).IsCardinalAccessible κ :=
  fixed_rank_of_representative_arrow_bound M κ s h

example :
    ∃ (μ : Cardinal.{w}) (_ : Fact μ.IsRegular),
      IsCardinalAccessibleCategory M μ ∧ IsCardinalAccessibleCategory (D ⥤ M) μ ∧
      (∀ d : D, (Completeness.cofree M κ s d).IsCardinalAccessible μ) ∧
      (∀ d e : D, (Completeness.homPower M κ s d e).IsCardinalAccessible μ) ∧
      (∀ d : D, (Completeness.cofree M κ s d).PreservesCardinalPresentable μ) ∧
      (∀ e : D, ((evaluation D M).obj e).PreservesCardinalPresentable μ) ∧
        ∀ d e : D, (Completeness.homPower M κ s d e).PreservesCardinalPresentable μ :=
  common_rank M κ s

example :
    ∃ (μ : Cardinal.{w}) (_ : Fact μ.IsRegular), κ ≤ μ ∧
      HasCardinalLT (Arrow S) μ ∧
      IsCardinalLocallyPresentable M μ ∧ IsCardinalLocallyPresentable (D ⥤ M) μ ∧
      (∀ d e : D, HasCardinalLT (e ⟶ d) μ) ∧
      (∀ d : D, (Completeness.cofree M κ s d).IsCardinalAccessible μ) ∧
        ∀ d e : D, (Completeness.homPower M κ s d e).IsCardinalAccessible μ :=
  bounded_common_rank M κ s

example (d e : D) (μ ν : Cardinal.{w}) [Fact μ.IsRegular] [Fact ν.IsRegular]
    (h : μ ≤ ν) [(Completeness.homPower M κ s d e).IsCardinalAccessible μ] :
    (Completeness.homPower M κ s d e).IsCardinalAccessible ν :=
  Functor.isCardinalAccessible_of_le _ h

example (d e : D) (μ : Cardinal.{w}) [Fact μ.IsRegular] (hκ : κ ≤ μ)
    (h : HasCardinalLT (e ⟶ d) μ) (J : Type w) [SmallCategory J] [IsCardinalFiltered J μ]
    (F : J ⥤ M) (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((Completeness.homPower M κ s d e).mapCocone c) := by
  let : (Completeness.homPower M κ s d e).IsCardinalAccessible μ :=
    homPower_isCardinalAccessible_of_hom_bound M κ s d e μ hκ h
  let : PreservesColimitsOfShape J (Completeness.homPower M κ s d e) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ μ J
  exact isColimitOfPreserves _ hc

example (d : D) (μ : Cardinal.{w}) [Fact μ.IsRegular] (hκ : κ ≤ μ)
    (h : ∀ e : D, HasCardinalLT (e ⟶ d) μ)
    (J : Type w) [SmallCategory J] [IsCardinalFiltered J μ]
    (F : J ⥤ M) (c : Cocone F) (hc : IsColimit c) :
    IsColimit ((Completeness.cofree M κ s d).mapCocone c) := by
  let : (Completeness.cofree M κ s d).IsCardinalAccessible μ :=
    cofree_isCardinalAccessible_of_hom_bounds M κ s d μ hκ h
  let : PreservesColimitsOfShape J (Completeness.cofree M κ s d) :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible _ μ J
  exact isColimitOfPreserves _ hc

end ActualRanks

section Concrete

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- An infinite original discrete index keeps fixed aleph0 because each actual Hom type is finite. -/
example (d : Discrete ℕ) :
    Functor.IsCardinalAccessible (Completeness.cofree (Type) Cardinal.aleph0.{0}
      (equivSmallModel.{0} (Discrete ℕ)) d)
        Cardinal.aleph0.{0} :=
  cofree_isCardinalAccessible_of_hom_bounds (Type) Cardinal.aleph0.{0} _ d _
    le_rfl (fun e ↦ hasCardinalLT_of_finite (e ⟶ d) _ le_rfl)

example (d e : Discrete ℕ) :
    Functor.IsCardinalAccessible (Completeness.homPower (Type) Cardinal.aleph0.{0}
      (equivSmallModel.{0} (Discrete ℕ)) d e)
        Cardinal.aleph0.{0} :=
  homPower_isCardinalAccessible_fixed (Type) Cardinal.aleph0.{0} _ d e
    (hasCardinalLT_of_finite (e ⟶ d) _ le_rfl)

/-- Raised original objects and Hom universe do not change the working coefficient universe. -/
example (d e : Discrete (ULift.{1} ℕ)) :
    Functor.IsCardinalAccessible (Completeness.homPower (Type) Cardinal.aleph0.{0}
      (equivSmallModel.{0} (Discrete (ULift.{1} ℕ))) d e)
        Cardinal.aleph0.{0} :=
  homPower_isCardinalAccessible_fixed (Type) Cardinal.aleph0.{0} _ d e
    (hasCardinalLT_of_finite (e ⟶ d) _ le_rfl)

example :
    ∃ (μ : Cardinal.{0}) (_ : Fact μ.IsRegular), Cardinal.aleph0.{0} ≤ μ ∧
      ∀ d e : Discrete PEmpty.{1},
        (Completeness.homPower (Type) Cardinal.aleph0.{0}
          (equivSmallModel.{0} (Discrete PEmpty.{1})) d e).IsCardinalAccessible μ := by
  obtain ⟨μ, _, hκ, _, _, _, _, _, hPower⟩ := bounded_common_rank (Type) Cardinal.aleph0.{0}
    (equivSmallModel.{0} (Discrete PEmpty.{1}))
  exact ⟨μ, inferInstance, hκ, hPower⟩

/-- The nonthin original category has genuinely infinite Hom labels, so the bound is enlarged. -/
abbrev Nonthin := SingleObj ℕ

example :
    ¬ HasCardinalLT ((SingleObj.star ℕ : Nonthin) ⟶ SingleObj.star ℕ) Cardinal.aleph0.{0} := by
  change ¬ HasCardinalLT ℕ Cardinal.aleph0.{0}
  simp only [hasCardinalLT_aleph0_iff]
  intro h
  let : Finite ℕ := h
  exact not_finite ℕ

example :
    ∃ (μ : Cardinal.{0}) (_ : Fact μ.IsRegular), Cardinal.aleph0.{0} ≤ μ ∧
      (∀ d e : Nonthin, HasCardinalLT (e ⟶ d) μ) ∧
      ∀ d e : Nonthin,
        Functor.IsCardinalAccessible (Completeness.homPower (Type) Cardinal.aleph0.{0}
          (equivSmallModel.{0} Nonthin) d e)
            μ := by
  obtain ⟨μ, _, hκ, _, _, _, hHom, _, hPower⟩ := bounded_common_rank (Type) Cardinal.aleph0.{0}
    (equivSmallModel.{0} Nonthin)
  exact ⟨μ, inferInstance, hκ, hHom, hPower⟩

/-- Here only the ORIGINAL Hom universe is raised above the working universe. -/
abbrev RaisedHoms := SingleObj (ULift.{1} ℕ)

local instance : LocallySmall.{0} RaisedHoms where
  hom_small _ _ := by
    change Small.{0} (ULift.{1} ℕ)
    exact small_of_injective (f := ULift.down) ULift.down_injective

example (d e : RaisedHoms) :
    Functor.IsAccessible.{0}
      (Completeness.homPower (Type) Cardinal.aleph0.{0}
        (equivSmallModel.{0} RaisedHoms) d e) :=
  homPower_isAccessible (Type) Cardinal.aleph0.{0} _ d e

/-- Multiplication by minus one is a nonidentity original index automorphism. -/
def signIso : SingleObj.star ℤ ≅ SingleObj.star ℤ where
  hom := (-1 : ℤ)
  inv := (-1 : ℤ)
  hom_inv_id := by change (-1 : ℤ) * (-1) = 1; decide
  inv_hom_id := by change (-1 : ℤ) * (-1) = 1; decide

example :
    homLabelEquiv signIso (SingleObj.star ℤ) (2 : ℤ) = (-2 : ℤ) := by
  rw [homLabelEquiv_apply]
  change (-1 : ℤ) * 2 = -2
  decide

example :
    (homLabelEquiv signIso (SingleObj.star ℤ)).symm (2 : ℤ) = (-2 : ℤ) := by
  rw [homLabelEquiv_symm_apply]
  change (-1 : ℤ) * 2 = -2
  decide

example (X : Type) :
    let s := equivSmallModel.{0} (SingleObj ℤ)
    let _ : HasProductsOfShape (SingleObj.star ℤ ⟶ SingleObj.star ℤ) (Type) :=
      Completeness.homProducts (Type) Cardinal.aleph0.{0} s _ _
    (componentIso (Type) Cardinal.aleph0.{0} s signIso X (SingleObj.star ℤ)).hom ≫
        Pi.π (fun _ : ℤ ↦ X) 2 = Pi.π (fun _ : ℤ ↦ X) (-2) := by
  let s := equivSmallModel.{0} (SingleObj ℤ)
  let _ : HasProductsOfShape ℤ (Type) :=
    Completeness.homProducts (Type) Cardinal.aleph0.{0} s (SingleObj.star ℤ) (SingleObj.star ℤ)
  let m : (∏ᶜ fun _ : ℤ ↦ X) ⟶ ∏ᶜ fun _ : ℤ ↦ X :=
    (componentIso (Type) Cardinal.aleph0.{0} s signIso X (SingleObj.star ℤ)).hom
  let h₂ : SingleObj.star ℤ ⟶ SingleObj.star ℤ := (2 : ℤ)
  change m ≫ Pi.π (fun _ : ℤ ↦ X) 2 = Pi.π (fun _ : ℤ ↦ X) (-2)
  have hi : m ≫ Pi.π (fun _ : ℤ ↦ X) 2 =
      Pi.π (fun _ : ℤ ↦ X) (h₂ ≫ signIso.inv) :=
    componentIso_hom_π (Type) Cardinal.aleph0.{0} s signIso X (SingleObj.star ℤ) (2 : ℤ)
  have hlabel : h₂ ≫ signIso.inv = (-2 : ℤ) := by
    change (-1 : ℤ) * 2 = -2
    decide
  rw [hlabel] at hi
  exact hi

/-- Two actual infinite-Hom product points are distinct, and the SAME native Hom-power
coefficient collapse identifies them. This checks the full map, not just its object type. -/
theorem collapse_erases_distinction :
    let s := equivSmallModel.{0} Nonthin
    let R := Completeness.homPower (Type) Cardinal.aleph0.{0} s
      (SingleObj.star ℕ) (SingleObj.star ℕ)
    ∃ u v : (PUnit : Type) ⟶ R.obj Bool, u ≠ v ∧
      u ≫ R.map (↾fun _ : Bool ↦ PUnit.unit) =
        v ≫ R.map (↾fun _ : Bool ↦ PUnit.unit) := by
  let s := equivSmallModel.{0} Nonthin
  let _ : HasProductsOfShape ℕ (Type) :=
    Completeness.homProducts (Type) Cardinal.aleph0.{0} s (SingleObj.star ℕ) (SingleObj.star ℕ)
  let R := Completeness.homPower (Type) Cardinal.aleph0.{0} s
    (SingleObj.star ℕ) (SingleObj.star ℕ)
  let u : (PUnit : Type) ⟶ ∏ᶜ fun _ : ℕ ↦ Bool :=
    Pi.lift (fun _ : ℕ ↦ ↾fun _ : PUnit ↦ true)
  let v : (PUnit : Type) ⟶ ∏ᶜ fun _ : ℕ ↦ Bool :=
    Pi.lift (fun _ : ℕ ↦ ↾fun _ : PUnit ↦ false)
  let collapse : (Bool : Type) ⟶ PUnit := ↾fun _ ↦ PUnit.unit
  let c : (∏ᶜ fun _ : ℕ ↦ Bool) ⟶ ∏ᶜ fun _ : ℕ ↦ PUnit := R.map collapse
  have hu (h : ℕ) : u ≫ Pi.π (fun _ : ℕ ↦ Bool) h = ↾fun _ : PUnit ↦ true :=
    Pi.lift_comp_π _ _
  have hv (h : ℕ) : v ≫ Pi.π (fun _ : ℕ ↦ Bool) h = ↾fun _ : PUnit ↦ false :=
    Pi.lift_comp_π _ _
  refine ⟨u, v, ?_, ?_⟩
  · intro he
    have hp := congrArg (fun m : (PUnit : Type) ⟶ ∏ᶜ fun _ : ℕ ↦ Bool ↦
      m ≫ Pi.π (fun _ : ℕ ↦ Bool) 1) he
    rw [hu, hv] at hp
    have hx := congrArg (fun m : (PUnit : Type) ⟶ Bool ↦ m PUnit.unit) hp
    cases hx
  · change u ≫ c = v ≫ c
    apply Pi.hom_ext (u ≫ c) (v ≫ c)
    intro h
    have hc : c ≫ Pi.π (fun _ : ℕ ↦ PUnit) h =
        Pi.π (fun _ : ℕ ↦ Bool) h ≫ collapse :=
      Completeness.cofree_coefficient_map_π (Type) Cardinal.aleph0.{0} s
        (SingleObj.star ℕ) (SingleObj.star ℕ) collapse h
    rw [Category.assoc, hc, ← Category.assoc, hu,
      Category.assoc, hc, ← Category.assoc, hv]
    rfl


end Concrete

end CategoryTheory.Presentable.HomPowerAccessibilityTest
