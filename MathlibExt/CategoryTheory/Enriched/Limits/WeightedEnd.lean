/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.Basic
public import MathlibExt.CategoryTheory.Enriched.Representable
import MathlibExt.CategoryTheory.Enriched.Limits.Products
import Mathlib.CategoryTheory.Enriched.FunctorCategory
import Mathlib.CategoryTheory.Enriched.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Enriched weighted ends

The weighted end of two enriched functors is the equalizer of the two
hom-object naturality maps between object-indexed products of internal Homs.
Only an enrichment of the source is required, not a selected ordinary category.

## Public imports

The enriched monoidal/naturality API and representable functors are intentional
public dependencies.  Product and equalizer machinery remains an implementation
dependency of this presentation.
-/

set_option autoImplicit false

noncomputable section

@[expose] public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed BraidedCategory Opposite

universe uI vI uV vV uC vC

namespace CategoryTheory.Enriched

attribute [local instance] MonoidalClosed.enrichedCategorySelf

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
variable {I : Type uI} [EnrichedCategory V I]

private abbrev weightedEndObjects
    (W F : EnrichedFunctor V I V) (a : I) : V :=
  (ihom (W.obj a)).obj (F.obj a)

private abbrev weightedEndRelations
    (W F : EnrichedFunctor V I V) (p : I × I) : V :=
  (ihom ((p.1 ⟶[V] p.2) ⊗ W.obj p.1)).obj (F.obj p.2)

private abbrev weightedEndLeftRaw
    (W F : EnrichedFunctor V I V)
    [HasProduct (weightedEndObjects W F)] (a b : I) :
    (((a ⟶[V] b) ⊗ W.obj a) ⊗ ∏ᶜ weightedEndObjects W F) ⟶
      F.obj b :=
  (α_ ((a ⟶[V] b)) (W.obj a) (∏ᶜ weightedEndObjects W F)).hom ≫
    ((a ⟶[V] b) ◁
      ((W.obj a) ◁ Pi.π (weightedEndObjects W F) a)) ≫
    ((a ⟶[V] b) ◁ (ihom.ev (W.obj a)).app (F.obj a)) ≫
    (β_ (a ⟶[V] b) (F.obj a)).hom ≫
    MonoidalClosed.uncurry (F.map a b)

private abbrev weightedEndRightRaw
    (W F : EnrichedFunctor V I V)
    [HasProduct (weightedEndObjects W F)] (a b : I) :
    (((a ⟶[V] b) ⊗ W.obj a) ⊗ ∏ᶜ weightedEndObjects W F) ⟶
      F.obj b :=
  ((((β_ (a ⟶[V] b) (W.obj a)).hom ≫
      MonoidalClosed.uncurry (W.map a b)) ⊗ₘ
        𝟙 (∏ᶜ weightedEndObjects W F))) ≫
    ((W.obj b) ◁ Pi.π (weightedEndObjects W F) b) ≫
    (ihom.ev (W.obj b)).app (F.obj b)

private abbrev weightedEndLeft
    (W F : EnrichedFunctor V I V)
    [HasProduct (weightedEndObjects W F)]
    [HasProduct (weightedEndRelations W F)] :
    (∏ᶜ weightedEndObjects W F) ⟶ ∏ᶜ weightedEndRelations W F :=
  Pi.lift fun p => MonoidalClosed.curry (weightedEndLeftRaw W F p.1 p.2)

private abbrev weightedEndRight
    (W F : EnrichedFunctor V I V)
    [HasProduct (weightedEndObjects W F)]
    [HasProduct (weightedEndRelations W F)] :
    (∏ᶜ weightedEndObjects W F) ⟶ ∏ᶜ weightedEndRelations W F :=
  Pi.lift fun p => MonoidalClosed.curry (weightedEndRightRaw W F p.1 p.2)

/-- The enriched weighted end of `W` and `F`, presented as an equalizer of
the two hom-object naturality maps. -/
public abbrev weightedEnd (W F : EnrichedFunctor V I V) :
    let t : I → V := fun a ↦ (ihom (W.obj a)).obj (F.obj a)
    let s : I × I → V := fun p ↦
      (ihom ((p.1 ⟶[V] p.2) ⊗ W.obj p.1)).obj (F.obj p.2)
    let l [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (α_ (p.1 ⟶[V] p.2) (W.obj p.1) (∏ᶜ t)).hom ≫
          ((p.1 ⟶[V] p.2) ◁
            ((W.obj p.1) ◁ Pi.π t p.1)) ≫
          ((p.1 ⟶[V] p.2) ◁
            (ihom.ev (W.obj p.1)).app (F.obj p.1)) ≫
          (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
          MonoidalClosed.uncurry (F.map p.1 p.2)
    let r [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
            MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ 𝟙 (∏ᶜ t)) ≫
          ((W.obj p.2) ◁ Pi.π t p.2) ≫
          (ihom.ev (W.obj p.2)).app (F.obj p.2)
    ∀ [HasProduct t] [HasProduct s] [HasEqualizer l r], V := by
  dsimp only
  intro _ _ _
  exact equalizer
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (α_ (p.1 ⟶[V] p.2) (W.obj p.1)
          (∏ᶜ fun a : I ↦ (ihom (W.obj a)).obj (F.obj a))).hom ≫
        ((p.1 ⟶[V] p.2) ◁ ((W.obj p.1) ◁ Pi.π
          (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a)) p.1)) ≫
        ((p.1 ⟶[V] p.2) ◁
          (ihom.ev (W.obj p.1)).app (F.obj p.1)) ≫
        (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
        MonoidalClosed.uncurry (F.map p.1 p.2))
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
          MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ
            𝟙 (∏ᶜ fun a : I ↦ (ihom (W.obj a)).obj (F.obj a))) ≫
        ((W.obj p.2) ◁ Pi.π
          (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a)) p.2) ≫
        (ihom.ev (W.obj p.2)).app (F.obj p.2))

namespace weightedEnd

/-- The object-indexed product diagram of a weighted end. -/
public abbrev objects (W F : EnrichedFunctor V I V) : I → V :=
  fun a ↦ (ihom (W.obj a)).obj (F.obj a)

/-- The hom-object-indexed relation diagram of a weighted end. -/
public abbrev relations (W F : EnrichedFunctor V I V) : I × I → V :=
  fun p ↦ (ihom ((p.1 ⟶[V] p.2) ⊗ W.obj p.1)).obj (F.obj p.2)

/-- The parallel map expressing the diagram action in a weighted end. -/
public noncomputable abbrev leftMap (W F : EnrichedFunctor V I V)
    [HasProduct (objects W F)] [HasProduct (relations W F)] :
    (∏ᶜ objects W F) ⟶ ∏ᶜ relations W F :=
  Pi.lift fun p ↦ MonoidalClosed.curry <|
    (α_ (p.1 ⟶[V] p.2) (W.obj p.1) (∏ᶜ objects W F)).hom ≫
      ((p.1 ⟶[V] p.2) ◁
        ((W.obj p.1) ◁ Pi.π (objects W F) p.1)) ≫
      ((p.1 ⟶[V] p.2) ◁
        (ihom.ev (W.obj p.1)).app (F.obj p.1)) ≫
      (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
      MonoidalClosed.uncurry (F.map p.1 p.2)

/-- The parallel map expressing the weight action in a weighted end. -/
public noncomputable abbrev rightMap (W F : EnrichedFunctor V I V)
    [HasProduct (objects W F)] [HasProduct (relations W F)] :
    (∏ᶜ objects W F) ⟶ ∏ᶜ relations W F :=
  Pi.lift fun p ↦ MonoidalClosed.curry <|
    (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
        MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ
          𝟙 (∏ᶜ objects W F)) ≫
      ((W.obj p.2) ◁ Pi.π (objects W F) p.2) ≫
      (ihom.ev (W.obj p.2)).app (F.obj p.2)

variable (W F : EnrichedFunctor V I V)
  [HasProduct (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a))]
  [HasProduct (fun p : I × I ↦
    (ihom ((p.1 ⟶[V] p.2) ⊗ W.obj p.1)).obj (F.obj p.2))]
  [HasEqualizer
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (α_ (p.1 ⟶[V] p.2) (W.obj p.1)
          (∏ᶜ fun a : I ↦ (ihom (W.obj a)).obj (F.obj a))).hom ≫
        ((p.1 ⟶[V] p.2) ◁
          ((W.obj p.1) ◁ Pi.π
            (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a)) p.1)) ≫
        ((p.1 ⟶[V] p.2) ◁
          (ihom.ev (W.obj p.1)).app (F.obj p.1)) ≫
        (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
        MonoidalClosed.uncurry (F.map p.1 p.2))
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
          MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ
            𝟙 (∏ᶜ fun a : I ↦
              (ihom (W.obj a)).obj (F.obj a))) ≫
        ((W.obj p.2) ◁ Pi.π
          (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a)) p.2) ≫
        (ihom.ev (W.obj p.2)).app (F.obj p.2))]

/-- Projection from a weighted end to one internal-Hom component. -/
public def π (a : I) : weightedEnd W F ⟶ (ihom (W.obj a)).obj (F.obj a) :=
  equalizer.ι
      (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
        (α_ (p.1 ⟶[V] p.2) (W.obj p.1)
            (∏ᶜ fun a : I ↦ (ihom (W.obj a)).obj (F.obj a))).hom ≫
          ((p.1 ⟶[V] p.2) ◁ ((W.obj p.1) ◁ Pi.π
            (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a)) p.1)) ≫
          ((p.1 ⟶[V] p.2) ◁
            (ihom.ev (W.obj p.1)).app (F.obj p.1)) ≫
          (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
          MonoidalClosed.uncurry (F.map p.1 p.2))
      (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
        (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
            MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ
              𝟙 (∏ᶜ fun a : I ↦ (ihom (W.obj a)).obj (F.obj a))) ≫
          ((W.obj p.2) ◁ Pi.π
            (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a)) p.2) ≫
          (ihom.ev (W.obj p.2)).app (F.obj p.2)) ≫
    Pi.π (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a)) a

/-- The hom-object naturality equation satisfied by weighted-end projections. -/
public theorem condition (a b : I) :
    MonoidalClosed.curry
        (((α_ ((a ⟶[V] b)) (W.obj a) (weightedEnd W F)).hom ≫
          ((a ⟶[V] b) ◁ ((W.obj a) ◁ π W F a)) ≫
          ((a ⟶[V] b) ◁ (ihom.ev (W.obj a)).app (F.obj a)) ≫
          (β_ (a ⟶[V] b) (F.obj a)).hom ≫
          MonoidalClosed.uncurry (F.map a b))) =
      MonoidalClosed.curry
        (((((β_ (a ⟶[V] b) (W.obj a)).hom ≫
            MonoidalClosed.uncurry (W.map a b)) ⊗ₘ
              𝟙 (weightedEnd W F))) ≫
          ((W.obj b) ◁ π W F b) ≫
          (ihom.ev (W.obj b)).app (F.obj b)) := by
  let eι := equalizer.ι (weightedEndLeft W F) (weightedEndRight W F)
  let currentLeft : (((a ⟶[V] b) ⊗ W.obj a) ⊗ weightedEnd W F) ⟶
      F.obj b :=
    (α_ ((a ⟶[V] b)) (W.obj a) (weightedEnd W F)).hom ≫
      ((a ⟶[V] b) ◁ ((W.obj a) ◁ π W F a)) ≫
      ((a ⟶[V] b) ◁ (ihom.ev (W.obj a)).app (F.obj a)) ≫
      (β_ (a ⟶[V] b) (F.obj a)).hom ≫
      MonoidalClosed.uncurry (F.map a b)
  let currentRight : (((a ⟶[V] b) ⊗ W.obj a) ⊗ weightedEnd W F) ⟶
      F.obj b :=
    ((((β_ (a ⟶[V] b) (W.obj a)).hom ≫
        MonoidalClosed.uncurry (W.map a b)) ⊗ₘ
          𝟙 (weightedEnd W F))) ≫
      ((W.obj b) ◁ π W F b) ≫
      (ihom.ev (W.obj b)).app (F.obj b)
  change MonoidalClosed.curry currentLeft =
    MonoidalClosed.curry currentRight
  have hLeft :
      (((a ⟶[V] b) ⊗ W.obj a) ◁ eι) ≫
          weightedEndLeftRaw W F a b = currentLeft := by
    dsimp [eι, currentLeft, weightedEndLeftRaw, π]
    simp [Category.assoc]
  have hRight :
      (((a ⟶[V] b) ⊗ W.obj a) ◁ eι) ≫
          weightedEndRightRaw W F a b = currentRight := by
    dsimp [eι, currentRight, weightedEndRightRaw, π]
    rw [tensorHom_id, tensorHom_id]
    rw [whisker_exchange_assoc]
    rw [← whiskerLeft_comp_assoc]
  have h := equalizer.condition
    (weightedEndLeft W F) (weightedEndRight W F)
  have hp := congrArg
    (fun k => k ≫ Pi.π (weightedEndRelations W F) (a, b)) h
  have hp' : eι ≫ MonoidalClosed.curry (weightedEndLeftRaw W F a b) =
      eι ≫ MonoidalClosed.curry (weightedEndRightRaw W F a b) := by
    dsimp [eι]
    simpa [weightedEndLeft, weightedEndRight] using hp
  calc
    MonoidalClosed.curry currentLeft =
        MonoidalClosed.curry
          ((((a ⟶[V] b) ⊗ W.obj a) ◁ eι) ≫
            weightedEndLeftRaw W F a b) := congrArg _ hLeft.symm
    _ = eι ≫ MonoidalClosed.curry (weightedEndLeftRaw W F a b) :=
      MonoidalClosed.curry_natural_left _ _
    _ = eι ≫ MonoidalClosed.curry (weightedEndRightRaw W F a b) := hp'
    _ = MonoidalClosed.curry
          ((((a ⟶[V] b) ⊗ W.obj a) ◁ eι) ≫
            weightedEndRightRaw W F a b) :=
      (MonoidalClosed.curry_natural_left _ _).symm
    _ = MonoidalClosed.curry currentRight := congrArg _ hRight

/-- Lift a family of internal-Hom maps satisfying enriched naturality to the
weighted end. -/
@[no_expose]
public def lift {X : V}
    (p : ∀ a, X ⟶ (ihom (W.obj a)).obj (F.obj a))
    (h : ∀ (a b : I),
      MonoidalClosed.curry
          (((α_ ((a ⟶[V] b)) (W.obj a) X).hom ≫
            ((a ⟶[V] b) ◁ ((W.obj a) ◁ p a)) ≫
            ((a ⟶[V] b) ◁ (ihom.ev (W.obj a)).app (F.obj a)) ≫
            (β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b))) =
        MonoidalClosed.curry
          (((((β_ (a ⟶[V] b) (W.obj a)).hom ≫
              MonoidalClosed.uncurry (W.map a b)) ⊗ₘ 𝟙 X)) ≫
            ((W.obj b) ◁ p b) ≫
            (ihom.ev (W.obj b)).app (F.obj b))) :
    X ⟶ weightedEnd W F :=
  equalizer.lift (Pi.lift p) (by
    apply Pi.hom_ext
    rintro ⟨a, b⟩
    simp only [Category.assoc]
    rw [Pi.lift_comp_π, Pi.lift_comp_π]
    rw [← MonoidalClosed.curry_natural_left,
      ← MonoidalClosed.curry_natural_left]
    have hLeft :
        (((a ⟶[V] b) ⊗ W.obj a) ◁ Pi.lift p) ≫
            weightedEndLeftRaw W F a b =
          (α_ ((a ⟶[V] b)) (W.obj a) X).hom ≫
            ((a ⟶[V] b) ◁ ((W.obj a) ◁ p a)) ≫
            ((a ⟶[V] b) ◁ (ihom.ev (W.obj a)).app (F.obj a)) ≫
            (β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b) := by
      dsimp [weightedEndLeftRaw]
      rw [associator_naturality_right_assoc]
      rw [← whiskerLeft_comp_assoc]
      rw [← whiskerLeft_comp]
      rw [Pi.lift_comp_π]
    have hRight :
        (((a ⟶[V] b) ⊗ W.obj a) ◁ Pi.lift p) ≫
            weightedEndRightRaw W F a b =
          ((((β_ (a ⟶[V] b) (W.obj a)).hom ≫
              MonoidalClosed.uncurry (W.map a b)) ⊗ₘ 𝟙 X)) ≫
            ((W.obj b) ◁ p b) ≫
            (ihom.ev (W.obj b)).app (F.obj b) := by
      dsimp [weightedEndRightRaw]
      rw [tensorHom_id, tensorHom_id]
      rw [whisker_exchange_assoc]
      rw [← whiskerLeft_comp_assoc]
      rw [Pi.lift_comp_π]
    rw [hLeft, hRight]
    exact h a b)

/-- The lift has the prescribed weighted-end projections. -/
@[simp, reassoc]
public theorem lift_π {X : V}
    (p : ∀ a, X ⟶ (ihom (W.obj a)).obj (F.obj a))
    (h : ∀ (a b : I),
      MonoidalClosed.curry
          (((α_ ((a ⟶[V] b)) (W.obj a) X).hom ≫
            ((a ⟶[V] b) ◁ ((W.obj a) ◁ p a)) ≫
            ((a ⟶[V] b) ◁ (ihom.ev (W.obj a)).app (F.obj a)) ≫
            (β_ (a ⟶[V] b) (F.obj a)).hom ≫
            MonoidalClosed.uncurry (F.map a b))) =
        MonoidalClosed.curry
          (((((β_ (a ⟶[V] b) (W.obj a)).hom ≫
              MonoidalClosed.uncurry (W.map a b)) ⊗ₘ 𝟙 X)) ≫
            ((W.obj b) ◁ p b) ≫
            (ihom.ev (W.obj b)).app (F.obj b))) (a : I) :
    lift W F p h ≫ π W F a = p a := by
  simp [lift, π]

/-- Maps into a weighted end are equal when all projections agree. -/
public theorem hom_ext {X : V} {f g : X ⟶ weightedEnd W F}
    (h : ∀ a, f ≫ π W F a = g ≫ π W F a) : f = g := by
  apply equalizer.hom_ext
  apply Pi.hom_ext
  intro a
  simpa [π, Category.assoc] using h a

end weightedEnd

omit [BraidedCategory V] in
private theorem tensorUncurry_comp
    {K H X Y Z : V}
    (f : K ⟶ (ihom X).obj Y) (g : H ⟶ (ihom Y).obj Z) :
    X ◁ (f ⊗ₘ g) ≫ MonoidalClosed.compTranspose X Y Z =
      (α_ X K H).inv ≫
        MonoidalClosed.uncurry f ▷ H ≫
        MonoidalClosed.uncurry g := by
  rw [← MonoidalClosed.curry_uncurry f,
    ← MonoidalClosed.curry_uncurry g]
  symm
  simp only [MonoidalClosed.compTranspose_eq, tensorHom_def,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [MonoidalCategory.tensor_whiskerLeft_symm_assoc]
  have hα :
      (α_ X ((ihom X).obj Y) ((ihom Y).obj Z)).hom ≫
        (α_ X ((ihom X).obj Y) ((ihom Y).obj Z)).inv = 𝟙 _ := by
    exact Iso.hom_inv_id _
  slice_rhs 4 5 => rw [hα]
  rw [associator_inv_naturality_middle_assoc]
  rw [cancel_epi (α_ X K H).inv]
  simp only [Category.id_comp]
  rw [whisker_exchange_assoc]
  rw [← comp_whiskerRight_assoc]
  rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  simp only [Functor.id_obj]
  rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  simp only [MonoidalClosed.uncurry_curry]

private abbrev covariantRepresentable (c : I) : EnrichedFunctor V I V :=
  EnrichedFunctor.covariantRepresentable V I c

private def yonedaComponent (c : I) (F : EnrichedFunctor V I V)
    (a : I) : F.obj c ⟶ (ihom (c ⟶[V] a)).obj (F.obj a) :=
  MonoidalClosed.curry <|
    (β_ (c ⟶[V] a) (F.obj c)).hom ≫
      MonoidalClosed.uncurry (F.map c a)

private theorem yonedaComponent_condition
    (c : I) (F : EnrichedFunctor V I V) (a b : I) :
    MonoidalClosed.curry
        (((α_ (a ⟶[V] b) (c ⟶[V] a) (F.obj c)).hom ≫
          (a ⟶[V] b) ◁ ((c ⟶[V] a) ◁ yonedaComponent c F a) ≫
          (a ⟶[V] b) ◁ (ihom.ev (c ⟶[V] a)).app (F.obj a) ≫
          (β_ (a ⟶[V] b) (F.obj a)).hom ≫
          MonoidalClosed.uncurry (F.map a b))) =
      MonoidalClosed.curry
        (((((β_ (a ⟶[V] b) (c ⟶[V] a)).hom ≫
            MonoidalClosed.uncurry ((covariantRepresentable c).map a b)) ⊗ₘ
              𝟙 (F.obj c))) ≫
          ((c ⟶[V] b) ◁ yonedaComponent c F b) ≫
          (ihom.ev (c ⟶[V] b)).app (F.obj b)) := by
  apply MonoidalClosed.uncurry_injective
  dsimp [yonedaComponent, covariantRepresentable]
  simp only [MonoidalClosed.uncurry_curry]
  slice_lhs 2 3 =>
    rw [← whiskerLeft_comp,
      MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  have hm := F.map_comp c a b
  have hu := congrArg MonoidalClosed.uncurry hm
  simp only [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.enrichedCategorySelf_comp,
    MonoidalClosed.comp_eq,
    MonoidalClosed.uncurry_curry] at hu
  let r : (((a ⟶[V] b) ⊗ (c ⟶[V] a)) ⊗ F.obj c) ⟶
      (F.obj c ⊗ ((c ⟶[V] a) ⊗ (a ⟶[V] b))) :=
    ((β_ (a ⟶[V] b) (c ⟶[V] a)).hom ⊗ₘ 𝟙 (F.obj c)) ≫
      (β_ ((c ⟶[V] a) ⊗ (a ⟶[V] b)) (F.obj c)).hom
  have hur := congrArg (fun k => r ≫ k) hu
  dsimp [r] at hur
  simp only [MonoidalClosed.compTranspose_eq] at hur
  have hRight :
      (((β_ (a ⟶[V] b) (c ⟶[V] a)).hom ≫
            eComp V c a b ⊗ₘ 𝟙 (F.obj c)) ≫
          (β_ (c ⟶[V] b) (F.obj c)).hom ≫
          MonoidalClosed.uncurry (F.map c b)) =
        r ≫ F.obj c ◁ eComp V c a b ≫
          MonoidalClosed.uncurry (F.map c b) := by
    dsimp [r]
    have ht :
        (((β_ (a ⟶[V] b) (c ⟶[V] a)).hom ≫
              eComp V c a b) ⊗ₘ 𝟙 (F.obj c)) =
          ((β_ (a ⟶[V] b) (c ⟶[V] a)).hom ⊗ₘ
              𝟙 (F.obj c)) ≫
            (eComp V c a b ⊗ₘ 𝟙 (F.obj c)) := by
      rw [tensorHom_comp_tensorHom]
      simp
    rw [ht]
    simp only [Category.assoc]
    rw [BraidedCategory.braiding_naturality_assoc]
    simp only [id_tensorHom]
  have hLeft :
      ((α_ (a ⟶[V] b) (c ⟶[V] a) (F.obj c)).hom ≫
          (a ⟶[V] b) ◁
            ((β_ (c ⟶[V] a) (F.obj c)).hom ≫
              MonoidalClosed.uncurry (F.map c a)) ≫
          (β_ (a ⟶[V] b) (F.obj a)).hom ≫
          MonoidalClosed.uncurry (F.map a b)) =
        r ≫ F.obj c ◁ (F.map c a ⊗ₘ F.map a b) ≫
          MonoidalClosed.compTranspose
            (F.obj c) (F.obj a) (F.obj b) := by
    dsimp [r]
    rw [tensorUncurry_comp]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [BraidedCategory.braiding_naturality_right_assoc]
    have hBraid :
        (α_ (a ⟶[V] b) (c ⟶[V] a) (F.obj c)).hom ≫
            (a ⟶[V] b) ◁ (β_ (c ⟶[V] a) (F.obj c)).hom ≫
            (β_ (a ⟶[V] b) (F.obj c ⊗ (c ⟶[V] a))).hom =
          ((β_ (a ⟶[V] b) (c ⟶[V] a)).hom ▷ F.obj c) ≫
            (β_ ((c ⟶[V] a) ⊗ (a ⟶[V] b)) (F.obj c)).hom ≫
            (α_ (F.obj c) (c ⟶[V] a) (a ⟶[V] b)).inv := by
      have hy := BraidedCategory.yang_baxter
        (a ⟶[V] b) (c ⟶[V] a) (F.obj c)
      have hy' := congrArg
        (fun k =>
          (α_ (a ⟶[V] b) (c ⟶[V] a) (F.obj c)).hom ≫
            k ≫
            (α_ (F.obj c) (c ⟶[V] a) (a ⟶[V] b)).inv) hy
      simp only [Category.assoc, Iso.hom_inv_id_assoc] at hy'
      rw [BraidedCategory.braiding_tensor_right_hom,
        BraidedCategory.braiding_tensor_left_hom]
      simp only [Category.assoc]
      exact hy'.symm
    slice_lhs 1 3 => rw [hBraid]
    simp only [tensorHom_id, Category.assoc]
  simpa only [Category.assoc] using
    hLeft.trans (hur.symm.trans hRight.symm)

namespace weightedEnd

/- The parameterized Yoneda action is needed before any representable end
exists; the complete relation is already used by the end construction. -/
/-- The canonical parameterized Yoneda family satisfies its full enriched
naturality relation without any end-existence assumption. -/
public theorem yonedaAction_condition (c : I) (F : EnrichedFunctor V I V) (a b : I) :
    (α_ (a ⟶[V] b) (c ⟶[V] a) (F.obj c)).hom ≫
      ((a ⟶[V] b) ◁
        ((β_ (c ⟶[V] a) (F.obj c)).hom ≫
          MonoidalClosed.uncurry (F.map c a))) ≫
      (β_ (a ⟶[V] b) (F.obj a)).hom ≫
      MonoidalClosed.uncurry (F.map a b) =
    (((β_ (a ⟶[V] b) (c ⟶[V] a)).hom ≫ eComp V c a b) ⊗ₘ 𝟙 (F.obj c)) ≫
      (β_ (c ⟶[V] b) (F.obj c)).hom ≫
      MonoidalClosed.uncurry (F.map c b) := by
  have h := congrArg MonoidalClosed.uncurry (yonedaComponent_condition c F a b)
  dsimp only [yonedaComponent, covariantRepresentable,
    EnrichedFunctor.covariantRepresentable] at h
  simp only [MonoidalClosed.uncurry_curry] at h
  conv_lhs at h =>
    slice 2 3
    rw [← whiskerLeft_comp, MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  rw [MonoidalClosed.whiskerLeft_curry_ihom_ev_app] at h
  simpa only [Category.assoc] using h

variable (W F : EnrichedFunctor V I V)
  [HasProduct (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a))]
  [HasProduct (fun p : I × I ↦
    (ihom ((p.1 ⟶[V] p.2) ⊗ W.obj p.1)).obj (F.obj p.2))]
  [HasEqualizer
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (α_ (p.1 ⟶[V] p.2) (W.obj p.1)
          (∏ᶜ fun a : I ↦ (ihom (W.obj a)).obj (F.obj a))).hom ≫
        ((p.1 ⟶[V] p.2) ◁
          ((W.obj p.1) ◁ Pi.π
            (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a)) p.1)) ≫
        ((p.1 ⟶[V] p.2) ◁
          (ihom.ev (W.obj p.1)).app (F.obj p.1)) ≫
        (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
        MonoidalClosed.uncurry (F.map p.1 p.2))
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
          MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ
            𝟙 (∏ᶜ fun a : I ↦
              (ihom (W.obj a)).obj (F.obj a))) ≫
        ((W.obj p.2) ◁ Pi.π
          (fun a : I ↦ (ihom (W.obj a)).obj (F.obj a)) p.2) ≫
        (ihom.ev (W.obj p.2)).app (F.obj p.2))]

/-- A graded enriched transformation of diagrams acts covariantly on the
weighted end. -/
@[no_expose]
public def mapDiagram (F' : EnrichedFunctor V I V)
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F') :
    let t : I → V := fun X ↦ (ihom (W.obj X)).obj (F'.obj X)
    let s : I × I → V := fun p ↦
      (ihom ((p.1 ⟶[V] p.2) ⊗ W.obj p.1)).obj (F'.obj p.2)
    let l [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (α_ (p.1 ⟶[V] p.2) (W.obj p.1) (∏ᶜ t)).hom ≫
          ((p.1 ⟶[V] p.2) ◁ ((W.obj p.1) ◁ Pi.π t p.1)) ≫
          ((p.1 ⟶[V] p.2) ◁
            (ihom.ev (W.obj p.1)).app (F'.obj p.1)) ≫
          (β_ (p.1 ⟶[V] p.2) (F'.obj p.1)).hom ≫
          MonoidalClosed.uncurry (F'.map p.1 p.2)
    let r [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
            MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ 𝟙 (∏ᶜ t)) ≫
          ((W.obj p.2) ◁ Pi.π t p.2) ≫
          (ihom.ev (W.obj p.2)).app (F'.obj p.2)
    ∀ [HasProduct t] [HasProduct s] [HasEqualizer l r],
      weightedEnd W F ⟶ equalizer l r := by
  dsimp only
  intro _ _ _
  let component (X : I) : F.obj X ⟶ F'.obj X :=
    (eHomEquiv V).symm (a.app X)
  exact lift W F'
    (fun X => π W F X ≫ (ihom (W.obj X)).map (component X))
    (by
      intro X Y
      apply MonoidalClosed.uncurry_injective
      simp only [MonoidalClosed.uncurry_curry]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      slice_lhs 3 4 =>
        rw [← whiskerLeft_comp, ihom.ev_naturality,
          whiskerLeft_comp]
      slice_rhs 3 4 =>
        rw [ihom.ev_naturality]
      have hc := congrArg MonoidalClosed.uncurry (condition W F X Y)
      simp only [MonoidalClosed.uncurry_curry] at hc
      have hc' := congrArg (fun k => k ≫ component Y) hc
      simp only [Category.assoc] at hc'
      rw [← hc']
      have hu :
          MonoidalClosed.uncurry (F.map X Y) ≫ component Y =
            component X ▷ (X ⟶[V] Y) ≫
              MonoidalClosed.uncurry (F'.map X Y) := by
        simpa only [component, tensorHom_id] using a.uncurriedNaturality X Y
      simp only [Category.assoc]
      have hbraid :
          ((X ⟶[V] Y) ◁ component X) ≫
              (β_ (X ⟶[V] Y) (F'.obj X)).hom =
            (β_ (X ⟶[V] Y) (F.obj X)).hom ≫
              component X ▷ (X ⟶[V] Y) := by
        exact BraidedCategory.braiding_naturality_right
          (X ⟶[V] Y) (component X)
      have hbraid' := congrArg
        (fun k => k ≫ MonoidalClosed.uncurry (F'.map X Y)) hbraid
      simp only [Category.assoc] at hbraid'
      have hu' := congrArg
        (fun k => (β_ (X ⟶[V] Y) (F.obj X)).hom ≫ k) hu
      rw [hbraid']
      rw [← hu'])

/-- Diagram maps commute with weighted-end projections. -/
@[simp, reassoc]
public theorem mapDiagram_π (F' : EnrichedFunctor V I V)
    :
    let t : I → V := fun X ↦ (ihom (W.obj X)).obj (F'.obj X)
    let s : I × I → V := fun p ↦
      (ihom ((p.1 ⟶[V] p.2) ⊗ W.obj p.1)).obj (F'.obj p.2)
    let l [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (α_ (p.1 ⟶[V] p.2) (W.obj p.1) (∏ᶜ t)).hom ≫
          ((p.1 ⟶[V] p.2) ◁ ((W.obj p.1) ◁ Pi.π t p.1)) ≫
          ((p.1 ⟶[V] p.2) ◁
            (ihom.ev (W.obj p.1)).app (F'.obj p.1)) ≫
          (β_ (p.1 ⟶[V] p.2) (F'.obj p.1)).hom ≫
          MonoidalClosed.uncurry (F'.map p.1 p.2)
    let r [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
            MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ 𝟙 (∏ᶜ t)) ≫
          ((W.obj p.2) ◁ Pi.π t p.2) ≫
          (ihom.ev (W.obj p.2)).app (F'.obj p.2)
    ∀ [HasProduct t] [HasProduct s] [HasEqualizer l r]
      (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F F')
      (X : I),
      mapDiagram W F F' a ≫ π W F' X =
        π W F X ≫
          (ihom (W.obj X)).map ((eHomEquiv V).symm (a.app X)) := by
  dsimp only
  intro _ _ _ a X
  simp [mapDiagram]

/-- Diagram variance preserves the unit-graded identity. -/
@[simp]
public theorem mapDiagram_id :
    mapDiagram W F F (GradedNatTrans.unitId F) = 𝟙 (weightedEnd W F) := by
  apply hom_ext W F
  intro X
  rw [mapDiagram_π, GradedNatTrans.unitId_component]
  simp

section DiagramComposition

variable (G H : EnrichedFunctor V I V)
  [HasProduct (fun X : I ↦ (ihom (W.obj X)).obj (G.obj X))]
  [HasProduct (fun p : I × I ↦
    (ihom ((p.1 ⟶[V] p.2) ⊗ W.obj p.1)).obj (G.obj p.2))]
  [HasEqualizer
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (α_ (p.1 ⟶[V] p.2) (W.obj p.1)
          (∏ᶜ fun X : I ↦ (ihom (W.obj X)).obj (G.obj X))).hom ≫
        ((p.1 ⟶[V] p.2) ◁ ((W.obj p.1) ◁ Pi.π
          (fun X : I ↦ (ihom (W.obj X)).obj (G.obj X)) p.1)) ≫
        ((p.1 ⟶[V] p.2) ◁
          (ihom.ev (W.obj p.1)).app (G.obj p.1)) ≫
        (β_ (p.1 ⟶[V] p.2) (G.obj p.1)).hom ≫
        MonoidalClosed.uncurry (G.map p.1 p.2))
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
          MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ
            𝟙 (∏ᶜ fun X : I ↦ (ihom (W.obj X)).obj (G.obj X))) ≫
        ((W.obj p.2) ◁ Pi.π
          (fun X : I ↦ (ihom (W.obj X)).obj (G.obj X)) p.2) ≫
        (ihom.ev (W.obj p.2)).app (G.obj p.2))]
  [HasProduct (fun X : I ↦ (ihom (W.obj X)).obj (H.obj X))]
  [HasProduct (fun p : I × I ↦
    (ihom ((p.1 ⟶[V] p.2) ⊗ W.obj p.1)).obj (H.obj p.2))]
  [HasEqualizer
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (α_ (p.1 ⟶[V] p.2) (W.obj p.1)
          (∏ᶜ fun X : I ↦ (ihom (W.obj X)).obj (H.obj X))).hom ≫
        ((p.1 ⟶[V] p.2) ◁ ((W.obj p.1) ◁ Pi.π
          (fun X : I ↦ (ihom (W.obj X)).obj (H.obj X)) p.1)) ≫
        ((p.1 ⟶[V] p.2) ◁
          (ihom.ev (W.obj p.1)).app (H.obj p.1)) ≫
        (β_ (p.1 ⟶[V] p.2) (H.obj p.1)).hom ≫
        MonoidalClosed.uncurry (H.map p.1 p.2))
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (((β_ (p.1 ⟶[V] p.2) (W.obj p.1)).hom ≫
          MonoidalClosed.uncurry (W.map p.1 p.2)) ⊗ₘ
            𝟙 (∏ᶜ fun X : I ↦ (ihom (W.obj X)).obj (H.obj X))) ≫
        ((W.obj p.2) ◁ Pi.π
          (fun X : I ↦ (ihom (W.obj X)).obj (H.obj X)) p.2) ≫
        (ihom.ev (W.obj p.2)).app (H.obj p.2))]

/-- Diagram variance preserves source-first unit-graded composition. -/
public theorem mapDiagram_comp
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) F G)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) G H) :
    mapDiagram W F G a ≫ mapDiagram W G H b =
      mapDiagram W F H (GradedNatTrans.unitComp a b) := by
  apply hom_ext W H
  intro X
  rw [Category.assoc, mapDiagram_π]
  rw [← Category.assoc, mapDiagram_π]
  rw [mapDiagram_π, GradedNatTrans.unitComp_component,
    Functor.map_comp]
  simp only [Category.assoc]

end DiagramComposition

/-- A graded enriched transformation of weights acts contravariantly on the
weighted end. -/
@[no_expose]
public def mapWeight (W' : EnrichedFunctor V I V)
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W' W) :
    let t : I → V := fun X ↦ (ihom (W'.obj X)).obj (F.obj X)
    let s : I × I → V := fun p ↦
      (ihom ((p.1 ⟶[V] p.2) ⊗ W'.obj p.1)).obj (F.obj p.2)
    let l [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (α_ (p.1 ⟶[V] p.2) (W'.obj p.1) (∏ᶜ t)).hom ≫
          ((p.1 ⟶[V] p.2) ◁ ((W'.obj p.1) ◁ Pi.π t p.1)) ≫
          ((p.1 ⟶[V] p.2) ◁
            (ihom.ev (W'.obj p.1)).app (F.obj p.1)) ≫
          (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
          MonoidalClosed.uncurry (F.map p.1 p.2)
    let r [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (((β_ (p.1 ⟶[V] p.2) (W'.obj p.1)).hom ≫
            MonoidalClosed.uncurry (W'.map p.1 p.2)) ⊗ₘ 𝟙 (∏ᶜ t)) ≫
          ((W'.obj p.2) ◁ Pi.π t p.2) ≫
          (ihom.ev (W'.obj p.2)).app (F.obj p.2)
    ∀ [HasProduct t] [HasProduct s] [HasEqualizer l r],
      weightedEnd W F ⟶ equalizer l r := by
  dsimp only
  intro _ _ _
  let component (X : I) : W'.obj X ⟶ W.obj X :=
    (eHomEquiv V).symm (a.app X)
  exact lift W' F
    (fun X => π W F X ≫
      (MonoidalClosed.pre (component X)).app (F.obj X))
    (by
      intro X Y
      apply MonoidalClosed.uncurry_injective
      simp only [MonoidalClosed.uncurry_curry]
      simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
      slice_lhs 3 4 =>
        rw [← whiskerLeft_comp,
          MonoidalClosed.id_tensor_pre_app_comp_ev,
          whiskerLeft_comp]
      have hc := congrArg MonoidalClosed.uncurry (condition W F X Y)
      simp only [MonoidalClosed.uncurry_curry] at hc
      have hu :
          MonoidalClosed.uncurry (W'.map X Y) ≫ component Y =
            component X ▷ (X ⟶[V] Y) ≫
              MonoidalClosed.uncurry (W.map X Y) := by
        simpa only [component, tensorHom_id] using a.uncurriedNaturality X Y
      let q : (((X ⟶[V] Y) ⊗ W'.obj X) ⊗ weightedEnd W F) ⟶
          (((X ⟶[V] Y) ⊗ W.obj X) ⊗ weightedEnd W F) :=
        ((𝟙 (X ⟶[V] Y) ⊗ₘ component X) ⊗ₘ
          𝟙 (weightedEnd W F))
      calc
        _ = q ≫
            ((α_ (X ⟶[V] Y) (W.obj X) (weightedEnd W F)).hom ≫
              (X ⟶[V] Y) ◁ W.obj X ◁ π W F X ≫
              (X ⟶[V] Y) ◁ (ihom.ev (W.obj X)).app (F.obj X) ≫
              (β_ (X ⟶[V] Y) (F.obj X)).hom ≫
              MonoidalClosed.uncurry (F.map X Y)) := by
                dsimp [q]
                simp only [Category.assoc]
                rw [MonoidalCategory.associator_naturality_assoc]
                simp only [id_tensorHom, tensorHom_id]
                rw [← whiskerLeft_comp_assoc]
                rw [whisker_exchange]
                rw [MonoidalCategory.whiskerLeft_comp]
                simp only [Category.assoc]
        _ = q ≫
            (((β_ (X ⟶[V] Y) (W.obj X)).hom ≫
                MonoidalClosed.uncurry (W.map X Y) ⊗ₘ
                  𝟙 (weightedEnd W F)) ≫
              W.obj Y ◁ π W F Y ≫
              (ihom.ev (W.obj Y)).app (F.obj Y)) := by
                rw [hc]
        _ = _ := by
          dsimp [q]
          slice_rhs 3 4 =>
            rw [MonoidalClosed.id_tensor_pre_app_comp_ev]
          have hbraid :
              (𝟙 (X ⟶[V] Y) ⊗ₘ component X) ≫
                  (β_ (X ⟶[V] Y) (W.obj X)).hom =
                (β_ (X ⟶[V] Y) (W'.obj X)).hom ≫
                  component X ▷ (X ⟶[V] Y) := by
            simpa only [id_tensorHom, tensorHom_id] using
              (BraidedCategory.braiding_naturality
                (𝟙 (X ⟶[V] Y)) (component X))
          have hFirst :
              (((𝟙 (X ⟶[V] Y) ⊗ₘ component X) ⊗ₘ
                    𝟙 (equalizer (weightedEndLeft W F) (weightedEndRight W F))) ≫
                (((β_ (X ⟶[V] Y) (W.obj X)).hom ≫
                    MonoidalClosed.uncurry (W.map X Y)) ⊗ₘ
                  𝟙 (equalizer (weightedEndLeft W F) (weightedEndRight W F)))) =
              ((((β_ (X ⟶[V] Y) (W'.obj X)).hom ≫
                    MonoidalClosed.uncurry (W'.map X Y)) ⊗ₘ
                  𝟙 (equalizer (weightedEndLeft W F) (weightedEndRight W F))) ≫
                (component Y ⊗ₘ
                  𝟙 (equalizer (weightedEndLeft W F) (weightedEndRight W F)))) := by
            rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
            simp only [Category.comp_id]
            rw [← Category.assoc, hbraid, Category.assoc, ← hu]
            simp only [Category.assoc]
          rw [← Category.assoc, hFirst]
          simp only [tensorHom_id, Category.assoc]
          rw [← whisker_exchange_assoc])

/-- Weight maps commute with weighted-end projections. -/
@[simp, reassoc]
public theorem mapWeight_π (W' : EnrichedFunctor V I V)
    :
    let t : I → V := fun X ↦ (ihom (W'.obj X)).obj (F.obj X)
    let s : I × I → V := fun p ↦
      (ihom ((p.1 ⟶[V] p.2) ⊗ W'.obj p.1)).obj (F.obj p.2)
    let l [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (α_ (p.1 ⟶[V] p.2) (W'.obj p.1) (∏ᶜ t)).hom ≫
          ((p.1 ⟶[V] p.2) ◁ ((W'.obj p.1) ◁ Pi.π t p.1)) ≫
          ((p.1 ⟶[V] p.2) ◁
            (ihom.ev (W'.obj p.1)).app (F.obj p.1)) ≫
          (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
          MonoidalClosed.uncurry (F.map p.1 p.2)
    let r [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (((β_ (p.1 ⟶[V] p.2) (W'.obj p.1)).hom ≫
            MonoidalClosed.uncurry (W'.map p.1 p.2)) ⊗ₘ 𝟙 (∏ᶜ t)) ≫
          ((W'.obj p.2) ◁ Pi.π t p.2) ≫
          (ihom.ev (W'.obj p.2)).app (F.obj p.2)
    ∀ [HasProduct t] [HasProduct s] [HasEqualizer l r]
      (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W' W)
      (X : I),
      mapWeight W F W' a ≫ π W' F X =
        π W F X ≫
          (MonoidalClosed.pre ((eHomEquiv V).symm (a.app X))).app (F.obj X) := by
  dsimp only
  intro _ _ _ a X
  simp [mapWeight]

/-- Weight variance preserves the unit-graded identity. -/
@[simp]
public theorem mapWeight_id :
    mapWeight W F W (GradedNatTrans.unitId W) = 𝟙 (weightedEnd W F) := by
  apply hom_ext W F
  intro X
  rw [mapWeight_π, GradedNatTrans.unitId_component]
  simp

section WeightComposition

variable (W' W'' : EnrichedFunctor V I V)
  [HasProduct (fun X : I ↦ (ihom (W'.obj X)).obj (F.obj X))]
  [HasProduct (fun p : I × I ↦
    (ihom ((p.1 ⟶[V] p.2) ⊗ W'.obj p.1)).obj (F.obj p.2))]
  [HasEqualizer
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (α_ (p.1 ⟶[V] p.2) (W'.obj p.1)
          (∏ᶜ fun X : I ↦ (ihom (W'.obj X)).obj (F.obj X))).hom ≫
        ((p.1 ⟶[V] p.2) ◁ ((W'.obj p.1) ◁ Pi.π
          (fun X : I ↦ (ihom (W'.obj X)).obj (F.obj X)) p.1)) ≫
        ((p.1 ⟶[V] p.2) ◁
          (ihom.ev (W'.obj p.1)).app (F.obj p.1)) ≫
        (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
        MonoidalClosed.uncurry (F.map p.1 p.2))
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (((β_ (p.1 ⟶[V] p.2) (W'.obj p.1)).hom ≫
          MonoidalClosed.uncurry (W'.map p.1 p.2)) ⊗ₘ
            𝟙 (∏ᶜ fun X : I ↦ (ihom (W'.obj X)).obj (F.obj X))) ≫
        ((W'.obj p.2) ◁ Pi.π
          (fun X : I ↦ (ihom (W'.obj X)).obj (F.obj X)) p.2) ≫
        (ihom.ev (W'.obj p.2)).app (F.obj p.2))]
  [HasProduct (fun X : I ↦ (ihom (W''.obj X)).obj (F.obj X))]
  [HasProduct (fun p : I × I ↦
    (ihom ((p.1 ⟶[V] p.2) ⊗ W''.obj p.1)).obj (F.obj p.2))]
  [HasEqualizer
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (α_ (p.1 ⟶[V] p.2) (W''.obj p.1)
          (∏ᶜ fun X : I ↦ (ihom (W''.obj X)).obj (F.obj X))).hom ≫
        ((p.1 ⟶[V] p.2) ◁ ((W''.obj p.1) ◁ Pi.π
          (fun X : I ↦ (ihom (W''.obj X)).obj (F.obj X)) p.1)) ≫
        ((p.1 ⟶[V] p.2) ◁
          (ihom.ev (W''.obj p.1)).app (F.obj p.1)) ≫
        (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
        MonoidalClosed.uncurry (F.map p.1 p.2))
    (Pi.lift fun p : I × I ↦ MonoidalClosed.curry <|
      (((β_ (p.1 ⟶[V] p.2) (W''.obj p.1)).hom ≫
          MonoidalClosed.uncurry (W''.map p.1 p.2)) ⊗ₘ
            𝟙 (∏ᶜ fun X : I ↦ (ihom (W''.obj X)).obj (F.obj X))) ≫
        ((W''.obj p.2) ◁ Pi.π
          (fun X : I ↦ (ihom (W''.obj X)).obj (F.obj X)) p.2) ≫
        (ihom.ev (W''.obj p.2)).app (F.obj p.2))]

/-- Contravariant weight variance preserves source-first unit-graded
composition, hence reverses the transformation order. -/
public theorem mapWeight_comp
    (a : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W' W)
    (b : GradedNatTrans ((Center.ofBraided V).obj (𝟙_ V)) W'' W') :
    mapWeight W F W' a ≫ mapWeight W' F W'' b =
      mapWeight W F W'' (GradedNatTrans.unitComp b a) := by
  apply hom_ext W'' F
  intro X
  rw [Category.assoc, mapWeight_π]
  rw [← Category.assoc, mapWeight_π]
  rw [mapWeight_π, GradedNatTrans.unitComp_component,
    MonoidalClosed.pre_map]
  simp only [NatTrans.comp_app, Category.assoc]

end WeightComposition


section RightKanEnd

variable {A : Type uI} [EnrichedCategory V A]
  {B : Type uC} [EnrichedCategory V B]

/-- The representable weight used by the pointwise enriched right-Kan end. -/
public abbrev rightKanWeight
    (u : EnrichedFunctor V A B) (b : B) : EnrichedFunctor V A V :=
  u.comp V (EnrichedFunctor.covariantRepresentable V B b)

omit [BraidedCategory V] in
private theorem rightKanWeight_map_uncurry
    (u : EnrichedFunctor V A B) (b : B) (a a' : A) :
    MonoidalClosed.uncurry ((rightKanWeight u b).map a a') =
      ((b ⟶[V] u.obj a) ◁ u.map a a') ≫
        eComp V b (u.obj a) (u.obj a') := by
  change MonoidalClosed.uncurry
      (u.map a a' ≫ MonoidalClosed.curry
        (eComp V b (u.obj a) (u.obj a'))) = _
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]

private abbrev rightKanPreBase (b c z : B) :
    (c ⟶[V] z) ⊗ (b ⟶[V] c) ⟶ (b ⟶[V] z) :=
  eComp V (op z) (op c) (op b)

omit [MonoidalClosed V] in
private theorem rightKanPreBase_eq (b c z : B) :
    rightKanPreBase (V := V) b c z =
      (β_ (c ⟶[V] z) (b ⟶[V] c)).hom ≫ eComp V b c z :=
  eComp_op_eq V (op b) (op c) (op z)

private def rightKanPostBase
    (u : EnrichedFunctor V A B) (b : B) (a a' : A) :
    (a ⟶[V] a') ⊗ (b ⟶[V] u.obj a) ⟶
      (b ⟶[V] u.obj a') :=
  (u.map a a' ⊗ₘ 𝟙 (b ⟶[V] u.obj a)) ≫
    rightKanPreBase b (u.obj a) (u.obj a')

private theorem rightKanPostBase_eq
    (u : EnrichedFunctor V A B) (b : B) (a a' : A) :
    rightKanPostBase u b a a' =
      (β_ (a ⟶[V] a') (b ⟶[V] u.obj a)).hom ≫
        MonoidalClosed.uncurry ((rightKanWeight u b).map a a') := by
  change
    (u.map a a' ⊗ₘ 𝟙 (b ⟶[V] u.obj a)) ≫
        rightKanPreBase b (u.obj a) (u.obj a') =
      (β_ (a ⟶[V] a') (b ⟶[V] u.obj a)).hom ≫
        MonoidalClosed.uncurry
          (u.map a a' ≫ MonoidalClosed.curry
            (eComp V b (u.obj a) (u.obj a')))
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry, rightKanPreBase_eq]
  simpa only [id_tensorHom, Category.assoc] using
    braiding_naturality_assoc
      (u.map a a') (𝟙 (b ⟶[V] u.obj a))
      (eComp V b (u.obj a) (u.obj a'))

omit [MonoidalClosed V] in
private theorem rightKanPostBase_eq_explicit
    (u : EnrichedFunctor V A B) (b : B) (a a' : A) :
    rightKanPostBase u b a a' =
      (β_ (a ⟶[V] a') (b ⟶[V] u.obj a)).hom ≫
        ((b ⟶[V] u.obj a) ◁ u.map a a') ≫
        eComp V b (u.obj a) (u.obj a') := by
  dsimp only [rightKanPostBase]
  rw [rightKanPreBase_eq]
  simpa only [id_tensorHom, Category.assoc] using
    braiding_naturality_assoc
      (u.map a a') (𝟙 (b ⟶[V] u.obj a))
      (eComp V b (u.obj a) (u.obj a'))

omit [MonoidalClosed V] in
private theorem rightKanPreBase_natural
    (u : EnrichedFunctor V A B) (b c : B) (a a' : A) :
    (a ⟶[V] a') ◁ rightKanPreBase b c (u.obj a) ≫
        rightKanPostBase u b a a' =
      (α_ (a ⟶[V] a') (c ⟶[V] u.obj a) (b ⟶[V] c)).inv ≫
        (rightKanPostBase u c a a' ▷ (b ⟶[V] c)) ≫
        rightKanPreBase b c (u.obj a') := by
  let U : V := u.obj a ⟶[V] u.obj a'
  let W₀ : V := c ⟶[V] u.obj a
  let R : V := b ⟶[V] c
  have ha :=
    (e_assoc V (op (u.obj a')) (op (u.obj a)) (op c) (op b)).symm
  have ha' :
      U ◁ rightKanPreBase b c (u.obj a) ≫
          rightKanPreBase b (u.obj a) (u.obj a') =
        (α_ U W₀ R).inv ≫
          (rightKanPreBase c (u.obj a) (u.obj a') ▷ R) ≫
          rightKanPreBase b c (u.obj a') := by
    change
      U ◁ rightKanPreBase b c (u.obj a) ≫
          rightKanPreBase b (u.obj a) (u.obj a') =
        (α_ U W₀ R).inv ≫
          (rightKanPreBase c (u.obj a) (u.obj a') ▷ R) ≫
          rightKanPreBase b c (u.obj a') at ha
    exact ha
  calc
    _ = (u.map a a' ▷ (W₀ ⊗ R)) ≫
        (U ◁ rightKanPreBase b c (u.obj a)) ≫
        rightKanPreBase b (u.obj a) (u.obj a') := by
      dsimp only [rightKanPostBase, U, W₀, R]
      simp only [tensorHom_id]
      rw [whisker_exchange_assoc]
    _ = (u.map a a' ▷ (W₀ ⊗ R)) ≫
        ((α_ U W₀ R).inv ≫
          (rightKanPreBase c (u.obj a) (u.obj a') ▷ R) ≫
          rightKanPreBase b c (u.obj a')) := by
      rw [ha']
    _ = _ := by
      dsimp only [rightKanPostBase, U, W₀, R]
      have hα := associator_inv_naturality_left_assoc
        (u.map a a') W₀ R
        ((rightKanPreBase c (u.obj a) (u.obj a') ▷ R) ≫
          rightKanPreBase b c (u.obj a'))
      simpa only [Category.assoc, comp_whiskerRight,
        tensorHom_id] using hα

private theorem rightKanPreBase_weight_natural
    (u : EnrichedFunctor V A B) (b c : B) (a a' : A) :
    (a ⟶[V] a') ◁ rightKanPreBase b c (u.obj a) ≫
        (β_ (a ⟶[V] a') ((rightKanWeight u b).obj a)).hom ≫
        MonoidalClosed.uncurry ((rightKanWeight u b).map a a') =
      (α_ (a ⟶[V] a') ((rightKanWeight u c).obj a)
          (b ⟶[V] c)).inv ≫
        (((β_ (a ⟶[V] a') ((rightKanWeight u c).obj a)).hom ≫
            MonoidalClosed.uncurry ((rightKanWeight u c).map a a')) ⊗ₘ
          𝟙 (b ⟶[V] c)) ≫
        rightKanPreBase b c (u.obj a') := by
  change
    (a ⟶[V] a') ◁ rightKanPreBase b c (u.obj a) ≫
        (β_ (a ⟶[V] a') (b ⟶[V] u.obj a)).hom ≫
        MonoidalClosed.uncurry
          (u.map a a' ≫ MonoidalClosed.curry
            (eComp V b (u.obj a) (u.obj a'))) =
      (α_ (a ⟶[V] a') (c ⟶[V] u.obj a)
          (b ⟶[V] c)).inv ≫
        (((β_ (a ⟶[V] a') (c ⟶[V] u.obj a)).hom ≫
          MonoidalClosed.uncurry
            (u.map a a' ≫ MonoidalClosed.curry
              (eComp V c (u.obj a) (u.obj a')))) ⊗ₘ
            𝟙 (b ⟶[V] c)) ≫
        rightKanPreBase b c (u.obj a')
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  rw [← rightKanPostBase_eq_explicit u b a a',
    ← rightKanPostBase_eq_explicit u c a a']
  simpa only [tensorHom_id] using
    rightKanPreBase_natural u b c a a'

omit [MonoidalClosed V] in
private theorem rightKanPreBase_id (b z : B) :
    (ρ_ (b ⟶[V] z)).inv ≫
        ((b ⟶[V] z) ◁ eId V b) ≫
        rightKanPreBase b b z =
      𝟙 (b ⟶[V] z) := by
  have hi := e_comp_id V (op z) (op b)
  rw [show eId V (op b) = eId V b from rfl] at hi
  change
    (ρ_ (b ⟶[V] z)).inv ≫
        ((b ⟶[V] z) ◁ eId V b) ≫
        rightKanPreBase b b z =
      𝟙 (b ⟶[V] z) at hi
  exact hi

omit [MonoidalClosed V] in
private theorem rightKanPreBase_comp (b c d z : B) :
    ((d ⟶[V] z) ◁ eComp V b c d) ≫
        rightKanPreBase b d z =
      ((d ⟶[V] z) ◁ (β_ (c ⟶[V] d) (b ⟶[V] c)).inv) ≫
        (α_ (d ⟶[V] z) (c ⟶[V] d) (b ⟶[V] c)).inv ≫
        (rightKanPreBase c d z ▷ (b ⟶[V] c)) ≫
        rightKanPreBase b c z := by
  let W : V := d ⟶[V] z
  let S : V := c ⟶[V] d
  let R : V := b ⟶[V] c
  have ha := (e_assoc V (op z) (op d) (op c) (op b)).symm
  have ha' :
      W ◁ rightKanPreBase b c d ≫ rightKanPreBase b d z =
        (α_ W S R).inv ≫
          (rightKanPreBase c d z ▷ R) ≫
          rightKanPreBase b c z := by
    change
      W ◁ rightKanPreBase b c d ≫ rightKanPreBase b d z =
        (α_ W S R).inv ≫
          (rightKanPreBase c d z ▷ R) ≫
          rightKanPreBase b c z at ha
    exact ha
  have hswap :
      (β_ S R).inv ≫ rightKanPreBase b c d = eComp V b c d := by
    rw [rightKanPreBase_eq, Iso.inv_hom_id_assoc]
  rw [← hswap, whiskerLeft_comp_assoc, ha']

variable (u : EnrichedFunctor V A B) (X : EnrichedFunctor V A V)
  [∀ b : B, HasProduct (objects (rightKanWeight u b) X)]
  [∀ b : B, HasProduct (relations (rightKanWeight u b) X)]
  [∀ b : B, HasEqualizer
    (leftMap (rightKanWeight u b) X)
    (rightMap (rightKanWeight u b) X)]

/-- The pointwise weighted end underlying the enriched right-Kan end functor. -/
public abbrev rightKanEndObject (b : B) : V :=
  weightedEnd (rightKanWeight u b) X

/-- The component of the target-index action on the right-Kan weighted end,
obtained by currying enriched precomposition followed by end projection and evaluation. -/
@[no_expose]
public def rightKanActionComponent (b c : B) (a : A) :
    ((b ⟶[V] c) ⊗ rightKanEndObject u X b) ⟶
      (ihom ((rightKanWeight u c).obj a)).obj (X.obj a) :=
  MonoidalClosed.curry <|
    (α_ ((rightKanWeight u c).obj a) (b ⟶[V] c)
      (rightKanEndObject u X b)).inv ≫
    (rightKanPreBase b c (u.obj a) ⊗ₘ
      𝟙 (rightKanEndObject u X b)) ≫
    ((rightKanWeight u b).obj a ◁
      π (rightKanWeight u b) X a) ≫
    (ihom.ev ((rightKanWeight u b).obj a)).app (X.obj a)

private theorem rightKanActionComponent_uncurry (b c : B) (a : A) :
    MonoidalClosed.uncurry (rightKanActionComponent u X b c a) =
      (α_ ((rightKanWeight u c).obj a) (b ⟶[V] c)
        (rightKanEndObject u X b)).inv ≫
      (rightKanPreBase b c (u.obj a) ⊗ₘ
        𝟙 (rightKanEndObject u X b)) ≫
      ((rightKanWeight u b).obj a ◁
        π (rightKanWeight u b) X a) ≫
      (ihom.ev ((rightKanWeight u b).obj a)).app (X.obj a) := by
  unfold rightKanActionComponent
  rw [MonoidalClosed.uncurry_curry]

/-- The full right-Kan action component is computed by the original
precomposition, end projection and internal-Hom evaluation. -/
public theorem rightKanActionComponent_uncurry_eq (b c : B) (a : A) :
    MonoidalClosed.uncurry (rightKanActionComponent u X b c a) =
      (α_ ((rightKanWeight u c).obj a) (b ⟶[V] c)
        (rightKanEndObject u X b)).inv ≫
      (((β_ (c ⟶[V] u.obj a) (b ⟶[V] c)).hom ≫
          eComp V b c (u.obj a)) ⊗ₘ 𝟙 (rightKanEndObject u X b)) ≫
      ((rightKanWeight u b).obj a ◁ π (rightKanWeight u b) X a) ≫
      (ihom.ev ((rightKanWeight u b).obj a)).app (X.obj a) := by
  rw [rightKanActionComponent_uncurry, rightKanPreBase_eq]
  rfl

private theorem rightKanActionComponent_condition
    (b c : B) (a a' : A) :
    MonoidalClosed.curry
        ((α_ (a ⟶[V] a') ((rightKanWeight u c).obj a)
            ((b ⟶[V] c) ⊗ rightKanEndObject u X b)).hom ≫
          ((a ⟶[V] a') ◁
            (((rightKanWeight u c).obj a) ◁
              rightKanActionComponent u X b c a)) ≫
          ((a ⟶[V] a') ◁
            (ihom.ev ((rightKanWeight u c).obj a)).app (X.obj a)) ≫
          (β_ (a ⟶[V] a') (X.obj a)).hom ≫
          MonoidalClosed.uncurry (X.map a a')) =
      MonoidalClosed.curry
        (((((β_ (a ⟶[V] a') ((rightKanWeight u c).obj a)).hom ≫
            MonoidalClosed.uncurry
              ((rightKanWeight u c).map a a')) ⊗ₘ
              𝟙 ((b ⟶[V] c) ⊗ rightKanEndObject u X b))) ≫
          (((rightKanWeight u c).obj a') ◁
            rightKanActionComponent u X b c a') ≫
          (ihom.ev ((rightKanWeight u c).obj a')).app (X.obj a')) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  slice_lhs 2 3 =>
    rw [← whiskerLeft_comp, ← MonoidalClosed.uncurry_eq,
      rightKanActionComponent_uncurry]
  slice_rhs 2 3 =>
    rw [← MonoidalClosed.uncurry_eq,
      rightKanActionComponent_uncurry]
  let H : V := a ⟶[V] a'
  let R : V := b ⟶[V] c
  let E : V := rightKanEndObject u X b
  let W₀ : A → V := fun i => (rightKanWeight u b).obj i
  let W₁ : A → V := fun i => c ⟶[V] u.obj i
  let q : ((H ⊗ W₁ a) ⊗ (R ⊗ E)) ⟶ ((H ⊗ W₀ a) ⊗ E) :=
    (α_ (H ⊗ W₁ a) R E).inv ≫
      ((α_ H (W₁ a) R).hom ▷ E) ≫
      ((H ◁ rightKanPreBase b c (u.obj a)) ▷ E)
  let endLeft : ((H ⊗ W₀ a) ⊗ E) ⟶ X.obj a' :=
    (α_ H (W₀ a) E).hom ≫
      (H ◁ (W₀ a ◁ π (rightKanWeight u b) X a)) ≫
      (H ◁ (ihom.ev (W₀ a)).app (X.obj a)) ≫
      (β_ H (X.obj a)).hom ≫
      MonoidalClosed.uncurry (X.map a a')
  let endRight : ((H ⊗ W₀ a) ⊗ E) ⟶ X.obj a' :=
    (((β_ H (W₀ a)).hom ≫
        MonoidalClosed.uncurry ((rightKanWeight u b).map a a')) ⊗ₘ
          𝟙 E) ≫
      (W₀ a' ◁ π (rightKanWeight u b) X a') ≫
      (ihom.ev (W₀ a')).app (X.obj a')
  have hc : endLeft = endRight := by
    have hc' := congrArg MonoidalClosed.uncurry
      (condition (rightKanWeight u b) X a a')
    rw [MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_curry] at hc'
    exact hc'
  have hLeft :
      (α_ H ((rightKanWeight u c).obj a) (R ⊗ E)).hom ≫
          (H ◁
            ((α_ ((rightKanWeight u c).obj a) R E).inv ≫
              (rightKanPreBase b c (u.obj a) ⊗ₘ 𝟙 E) ≫
              ((rightKanWeight u b).obj a ◁
                π (rightKanWeight u b) X a) ≫
              (ihom.ev ((rightKanWeight u b).obj a)).app (X.obj a))) ≫
          (β_ H (X.obj a)).hom ≫
          MonoidalClosed.uncurry (X.map a a') =
        q ≫ endLeft := by
    dsimp only [q, endLeft, H, R, E, W₀, W₁]
    monoidal
  rw [Category.assoc, hLeft, hc]
  have hBase :
      H ◁ rightKanPreBase b c (u.obj a) ≫
          (β_ H (W₀ a)).hom ≫
          MonoidalClosed.uncurry
            ((rightKanWeight u b).map a a') =
        (α_ H (W₁ a) R).inv ≫
          (((β_ H (W₁ a)).hom ≫
            MonoidalClosed.uncurry
              ((rightKanWeight u c).map a a')) ⊗ₘ 𝟙 R) ≫
          rightKanPreBase b c (u.obj a') := by
    exact rightKanPreBase_weight_natural u b c a a'
  have hBaseE := congrArg (fun k => k ⊗ₘ 𝟙 E) hBase
  have hBaseE' := congrArg
    (fun k =>
      (α_ (H ⊗ W₁ a) R E).inv ≫
        ((α_ H (W₁ a) R).hom ⊗ₘ 𝟙 E) ≫ k)
    hBaseE
  have hPrefix :
      q ≫
          (((β_ H (W₀ a)).hom ≫
            MonoidalClosed.uncurry
              ((rightKanWeight u b).map a a')) ⊗ₘ 𝟙 E) =
        (((β_ H (W₁ a)).hom ≫
            MonoidalClosed.uncurry
              ((rightKanWeight u c).map a a')) ⊗ₘ 𝟙 (R ⊗ E)) ≫
          (α_ (W₁ a') R E).inv ≫
          (rightKanPreBase b c (u.obj a') ⊗ₘ 𝟙 E) := by
    let midLeft : ((H ⊗ W₁ a) ⊗ (R ⊗ E)) ⟶ (W₀ a' ⊗ E) :=
      (α_ (H ⊗ W₁ a) R E).inv ≫
        ((α_ H (W₁ a) R).hom ⊗ₘ 𝟙 E) ≫
        (((H ◁ rightKanPreBase b c (u.obj a)) ≫
          (β_ H (W₀ a)).hom ≫
          MonoidalClosed.uncurry
            ((rightKanWeight u b).map a a')) ⊗ₘ 𝟙 E)
    let midRight : ((H ⊗ W₁ a) ⊗ (R ⊗ E)) ⟶ (W₀ a' ⊗ E) :=
      (α_ (H ⊗ W₁ a) R E).inv ≫
        ((α_ H (W₁ a) R).hom ⊗ₘ 𝟙 E) ≫
        (((α_ H (W₁ a) R).inv ≫
          (((β_ H (W₁ a)).hom ≫
            MonoidalClosed.uncurry
              ((rightKanWeight u c).map a a')) ⊗ₘ 𝟙 R) ≫
          rightKanPreBase b c (u.obj a')) ⊗ₘ 𝟙 E)
    have hStructLeft :
        q ≫
            (((β_ H (W₀ a)).hom ≫
              MonoidalClosed.uncurry
                ((rightKanWeight u b).map a a')) ⊗ₘ 𝟙 E) =
          midLeft := by
      dsimp only [q, midLeft, H, R, E, W₀, W₁]
      monoidal
    have hMiddle : midLeft = midRight := by
      change midLeft = midRight at hBaseE'
      exact hBaseE'
    have hStructRight :
        (((β_ H (W₁ a)).hom ≫
            MonoidalClosed.uncurry
              ((rightKanWeight u c).map a a')) ⊗ₘ 𝟙 (R ⊗ E)) ≫
          (α_ (W₁ a') R E).inv ≫
          (rightKanPreBase b c (u.obj a') ⊗ₘ 𝟙 E) =
        midRight := by
      dsimp only [midRight, H, R, E, W₀, W₁]
      monoidal
    exact hStructLeft.trans (hMiddle.trans hStructRight.symm)
  dsimp only [endRight]
  rw [← Category.assoc, hPrefix]
  let f : ((H ⊗ W₁ a) ⊗ (R ⊗ E)) ⟶ (W₁ a' ⊗ (R ⊗ E)) :=
    ((β_ H (W₁ a)).hom ≫
      MonoidalClosed.uncurry
        ((rightKanWeight u c).map a a')) ⊗ₘ 𝟙 (R ⊗ E)
  let g : (W₁ a' ⊗ (R ⊗ E)) ⟶ ((W₁ a' ⊗ R) ⊗ E) :=
    (α_ (W₁ a') R E).inv
  let h : ((W₁ a' ⊗ R) ⊗ E) ⟶ (W₀ a' ⊗ E) :=
    rightKanPreBase b c (u.obj a') ⊗ₘ 𝟙 E
  let k : (W₀ a' ⊗ E) ⟶
      (W₀ a' ⊗ (ihom (W₀ a')).obj (X.obj a')) :=
    W₀ a' ◁ π (rightKanWeight u b) X a'
  let l : (W₀ a' ⊗ (ihom (W₀ a')).obj (X.obj a')) ⟶ X.obj a' :=
    (ihom.ev (W₀ a')).app (X.obj a')
  change ((f ≫ g ≫ h) ≫ k ≫ l) = f ≫ g ≫ h ≫ k ≫ l
  simp only [Category.assoc]

/-- The grade-first action of an enriched target hom on the pointwise end. -/
@[no_expose]
public def rightKanEndAction (b c : B) :
    (b ⟶[V] c) ⊗ rightKanEndObject u X b ⟶
      rightKanEndObject u X c :=
  lift (rightKanWeight u c) X
    (rightKanActionComponent u X b c)
    (rightKanActionComponent_condition u X b c)

/-- The grade-first action is characterized by every weighted-end projection. -/
@[reassoc]
public theorem rightKanEndAction_π (b c : B) (a : A) :
    rightKanEndAction u X b c ≫ π (rightKanWeight u c) X a =
      rightKanActionComponent u X b c a :=
  lift_π (rightKanWeight u c) X _ _ a

private theorem rightKanEndAction_id (b : B) :
    (eId V b ▷ rightKanEndObject u X b) ≫
        rightKanEndAction u X b b =
      (λ_ (rightKanEndObject u X b)).hom := by
  apply hom_ext (rightKanWeight u b) X
  intro a
  rw [Category.assoc, rightKanEndAction_π]
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    rightKanActionComponent_uncurry,
    MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_eq]
  let W : V := (rightKanWeight u b).obj a
  let E : V := rightKanEndObject u X b
  have hId :
      (ρ_ W).inv ≫ W ◁ eId V b ≫
          rightKanPreBase b b (u.obj a) = 𝟙 W := by
    exact rightKanPreBase_id (V := V) b (u.obj a)
  have hIdE := congrArg (fun k => k ⊗ₘ 𝟙 E) hId
  have hPrefix :
      W ◁ (eId V b ▷ E) ≫
          (α_ W (b ⟶[V] b) E).inv ≫
          (rightKanPreBase b b (u.obj a) ⊗ₘ 𝟙 E) =
        W ◁ (λ_ E).hom := by
    let mid : W ⊗ (𝟙_ V ⊗ E) ⟶ W ⊗ E :=
      (W ◁ (λ_ E).hom) ≫
        (((ρ_ W).inv ≫ W ◁ eId V b ≫
          rightKanPreBase b b (u.obj a)) ⊗ₘ 𝟙 E)
    have hStruct :
        W ◁ (eId V b ▷ E) ≫
            (α_ W (b ⟶[V] b) E).inv ≫
            (rightKanPreBase b b (u.obj a) ⊗ₘ 𝟙 E) =
          mid := by
      dsimp only [mid, W, E]
      monoidal
    have hReduce : mid = W ◁ (λ_ E).hom := by
      have hIdE' := congrArg
        (fun k => (W ◁ (λ_ E).hom) ≫ k) hIdE
      have hUnit :
          (W ◁ (λ_ E).hom) ≫ (𝟙 W ⊗ₘ 𝟙 E) =
            W ◁ (λ_ E).hom := by simp
      change mid = (W ◁ (λ_ E).hom) ≫ (𝟙 W ⊗ₘ 𝟙 E) at hIdE'
      exact hIdE'.trans hUnit
    exact hStruct.trans hReduce
  slice_lhs 1 3 => rw [hPrefix]
  change
    W ◁ (λ_ E).hom ≫
        (W ◁ π (rightKanWeight u b) X a) ≫
        (ihom.ev W).app (X.obj a) =
      W ◁ (λ_ E).hom ≫
        (W ◁ π (rightKanWeight u b) X a) ≫
        (ihom.ev W).app (X.obj a)
  rfl

private theorem rightKanEndAction_comp (b c d : B) :
    (eComp V b c d ⊗ₘ 𝟙 (rightKanEndObject u X b)) ≫
        rightKanEndAction u X b d =
      ((β_ (c ⟶[V] d) (b ⟶[V] c)).inv ⊗ₘ
          𝟙 (rightKanEndObject u X b)) ≫
        (α_ (c ⟶[V] d) (b ⟶[V] c)
          (rightKanEndObject u X b)).hom ≫
        ((c ⟶[V] d) ◁ rightKanEndAction u X b c) ≫
        rightKanEndAction u X c d := by
  apply hom_ext (rightKanWeight u d) X
  intro a
  slice_lhs 2 3 => rw [rightKanEndAction_π]
  slice_rhs 4 5 => rw [rightKanEndAction_π]
  apply MonoidalClosed.uncurry_injective
  conv_lhs =>
    rw [MonoidalClosed.uncurry_natural_left,
      rightKanActionComponent_uncurry]
  conv_rhs =>
    rw [MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_natural_left,
      rightKanActionComponent_uncurry]
  let R : V := b ⟶[V] c
  let S : V := c ⟶[V] d
  let E₀ : V := rightKanEndObject u X b
  let E₁ : V := rightKanEndObject u X c
  let Wd : V := (rightKanWeight u d).obj a
  let Wc : V := (rightKanWeight u c).obj a
  let m : R ⊗ E₀ ⟶ E₁ := rightKanEndAction u X b c
  let p : Wd ⊗ S ⟶ Wc := rightKanPreBase c d (u.obj a)
  let pic : E₁ ⟶ (ihom Wc).obj (X.obj a) :=
    π (rightKanWeight u c) X a
  have hMove :
      Wd ◁ (S ◁ rightKanEndAction u X b c) ≫
          (α_ Wd S E₁).inv ≫
          (rightKanPreBase c d (u.obj a) ⊗ₘ 𝟙 E₁) ≫
          (Wc ◁ π (rightKanWeight u c) X a) ≫
          (ihom.ev Wc).app (X.obj a) =
        (α_ Wd S (R ⊗ E₀)).inv ≫
          (rightKanPreBase c d (u.obj a) ⊗ₘ 𝟙 (R ⊗ E₀)) ≫
          MonoidalClosed.uncurry
            (rightKanActionComponent u X b c a) := by
    change
      Wd ◁ (S ◁ m) ≫
          (α_ Wd S E₁).inv ≫
          (p ⊗ₘ 𝟙 E₁) ≫
          (Wc ◁ pic) ≫
          (ihom.ev Wc).app (X.obj a) =
        (α_ Wd S (R ⊗ E₀)).inv ≫
          (p ⊗ₘ 𝟙 (R ⊗ E₀)) ≫
          MonoidalClosed.uncurry
            (rightKanActionComponent u X b c a)
    calc
      _ = (α_ Wd S (R ⊗ E₀)).inv ≫
          (p ⊗ₘ 𝟙 (R ⊗ E₀)) ≫
          (Wc ◁ m) ≫
          (Wc ◁ pic) ≫
          (ihom.ev Wc).app (X.obj a) := by
        rw [associator_inv_naturality_right_assoc]
        have hex := whisker_exchange p m
        have hex' := congrArg
          (fun q =>
            (α_ Wd S (R ⊗ E₀)).inv ≫ q ≫
              (Wc ◁ pic) ≫ (ihom.ev Wc).app (X.obj a)) hex
        simpa only [id_tensorHom, tensorHom_id,
          Category.assoc] using hex'
      _ = (α_ Wd S (R ⊗ E₀)).inv ≫
          (p ⊗ₘ 𝟙 (R ⊗ E₀)) ≫
          (Wc ◁ rightKanActionComponent u X b c a) ≫
          (ihom.ev Wc).app (X.obj a) := by
        slice_lhs 3 4 =>
          rw [← whiskerLeft_comp]
          dsimp only [m, pic]
          rw [rightKanEndAction_π]
      _ = _ := by
        slice_lhs 3 4 => rw [← MonoidalClosed.uncurry_eq]
  change _ =
    Wd ◁ ((β_ S R).inv ⊗ₘ 𝟙 E₀) ≫
      (Wd ◁ (α_ S R E₀).hom) ≫
      (Wd ◁ (S ◁ rightKanEndAction u X b c)) ≫
      (α_ Wd S E₁).inv ≫
      (rightKanPreBase c d (u.obj a) ⊗ₘ 𝟙 E₁) ≫
      (Wc ◁ π (rightKanWeight u c) X a) ≫
      (ihom.ev Wc).app (X.obj a)
  slice_rhs 3 7 => rw [hMove]
  have hComp :
      MonoidalClosed.uncurry (rightKanActionComponent u X b c a) =
        (α_ Wc R E₀).inv ≫
          (rightKanPreBase b c (u.obj a) ⊗ₘ 𝟙 E₀) ≫
          ((rightKanWeight u b).obj a ◁
            π (rightKanWeight u b) X a) ≫
          (ihom.ev ((rightKanWeight u b).obj a)).app (X.obj a) := by
    exact rightKanActionComponent_uncurry u X b c a
  let pref :
      Wd ⊗ ((R ⊗ S) ⊗ E₀) ⟶ Wc ⊗ (R ⊗ E₀) :=
    Wd ◁ ((β_ S R).inv ⊗ₘ 𝟙 E₀) ≫
      (Wd ◁ (α_ S R E₀).hom) ≫
      (α_ Wd S (R ⊗ E₀)).inv ≫
      (rightKanPreBase c d (u.obj a) ⊗ₘ 𝟙 (R ⊗ E₀))
  have hPref :
      Wd ◁ ((β_ S R).inv ⊗ₘ 𝟙 E₀) ≫
          (Wd ◁ (α_ S R E₀).hom) ≫
          (α_ Wd S (R ⊗ E₀)).inv ≫
          (rightKanPreBase c d (u.obj a) ⊗ₘ 𝟙 (R ⊗ E₀)) ≫
          MonoidalClosed.uncurry
            (rightKanActionComponent u X b c a) =
        pref ≫ MonoidalClosed.uncurry
          (rightKanActionComponent u X b c a) := by
    dsimp only [pref]
    simp only [Category.assoc]
    rfl
  rw [hPref]
  rw [hComp]
  let Wb : V := (rightKanWeight u b).obj a
  let leftPrefix : Wd ⊗ ((R ⊗ S) ⊗ E₀) ⟶ Wb ⊗ E₀ :=
    Wd ◁ (eComp V b c d ⊗ₘ 𝟙 E₀) ≫
      (α_ Wd (b ⟶[V] d) E₀).inv ≫
      (rightKanPreBase b d (u.obj a) ⊗ₘ 𝟙 E₀)
  let rightPrefix : Wd ⊗ ((R ⊗ S) ⊗ E₀) ⟶ Wb ⊗ E₀ :=
    pref ≫
      (α_ Wc R E₀).inv ≫
      (rightKanPreBase b c (u.obj a) ⊗ₘ 𝟙 E₀)
  have hPre :
      Wd ◁ eComp V b c d ≫ rightKanPreBase b d (u.obj a) =
        (Wd ◁ (β_ S R).inv) ≫
          (α_ Wd S R).inv ≫
          (rightKanPreBase c d (u.obj a) ▷ R) ≫
          rightKanPreBase b c (u.obj a) := by
    exact rightKanPreBase_comp (V := V) b c d (u.obj a)
  have hPreE := congrArg (fun k => k ⊗ₘ 𝟙 E₀) hPre
  let midLeft : Wd ⊗ ((R ⊗ S) ⊗ E₀) ⟶ Wb ⊗ E₀ :=
    (α_ Wd (R ⊗ S) E₀).inv ≫
      ((Wd ◁ eComp V b c d ≫
        rightKanPreBase b d (u.obj a)) ⊗ₘ 𝟙 E₀)
  let midRight : Wd ⊗ ((R ⊗ S) ⊗ E₀) ⟶ Wb ⊗ E₀ :=
    (α_ Wd (R ⊗ S) E₀).inv ≫
      (((Wd ◁ (β_ S R).inv) ≫
        (α_ Wd S R).inv ≫
        (rightKanPreBase c d (u.obj a) ▷ R) ≫
        rightKanPreBase b c (u.obj a)) ⊗ₘ 𝟙 E₀)
  have hStructLeft : leftPrefix = midLeft := by
    dsimp only [leftPrefix, midLeft, Wd, Wb, R, S, E₀]
    monoidal
  have hMiddle : midLeft = midRight := by
    have h := congrArg
      (fun k => (α_ Wd (R ⊗ S) E₀).inv ≫ k) hPreE
    change midLeft = midRight at h
    exact h
  have hStructRight : rightPrefix = midRight := by
    dsimp only [rightPrefix, midRight, pref,
      Wd, Wc, Wb, R, S, E₀]
    monoidal
  have hPrefix : leftPrefix = rightPrefix :=
    hStructLeft.trans (hMiddle.trans hStructRight.symm)
  let suffix : Wb ⊗ E₀ ⟶ X.obj a :=
    (Wb ◁ π (rightKanWeight u b) X a) ≫
      (ihom.ev Wb).app (X.obj a)
  have hGoal := congrArg (fun k => k ≫ suffix) hPrefix
  convert hGoal using 1
  · simp
  · dsimp only [leftPrefix, suffix, Wd, Wb, E₀]
    simp only [Category.assoc, Functor.id_obj]
    rfl
  · dsimp only [rightPrefix, suffix, Wb, E₀]
    simp only [Category.assoc, Functor.id_obj]
    rfl

/-- The enriched hom map on the pointwise right-Kan end, with the inverse
outer braid dictated by the closed self-enrichment convention. -/
@[no_expose]
public def rightKanEndMap (b c : B) :
    (b ⟶[V] c) ⟶
      (ihom (rightKanEndObject u X b)).obj
        (rightKanEndObject u X c) :=
  MonoidalClosed.curry <|
    (β_ (b ⟶[V] c) (rightKanEndObject u X b)).inv ≫
      rightKanEndAction u X b c

/-- Uncurrying the end map recovers the inverse-braided grade-first action. -/
public theorem rightKanEndMap_uncurry (b c : B) :
    MonoidalClosed.uncurry (rightKanEndMap u X b c) =
      (β_ (b ⟶[V] c) (rightKanEndObject u X b)).inv ≫
        rightKanEndAction u X b c := by
  unfold rightKanEndMap
  rw [MonoidalClosed.uncurry_curry]

/-- The enriched parameter map preserves the enriched identity. -/
public theorem rightKanEndMap_id (b : B) :
    eId V b ≫ rightKanEndMap u X b b =
      eId V (rightKanEndObject u X b) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    rightKanEndMap_uncurry,
    MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq, MonoidalClosed.uncurry_curry]
  rw [braiding_inv_naturality_right_assoc]
  rw [rightKanEndAction_id]
  rw [← braiding_rightUnitor]
  simp

/-- The enriched parameter map preserves source-first enriched composition. -/
public theorem rightKanEndMap_comp (b c d : B) :
    eComp V b c d ≫ rightKanEndMap u X b d =
      (rightKanEndMap u X b c ⊗ₘ rightKanEndMap u X c d) ≫
        eComp V (rightKanEndObject u X b)
          (rightKanEndObject u X c) (rightKanEndObject u X d) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    rightKanEndMap_uncurry]
  conv_rhs =>
    rw [MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.enrichedCategorySelf_comp,
      MonoidalClosed.comp_eq, MonoidalClosed.uncurry_curry]
    rw [tensorUncurry_comp]
  rw [rightKanEndMap_uncurry, rightKanEndMap_uncurry]
  rw [braiding_inv_naturality_right_assoc]
  slice_lhs 2 3 =>
    rw [← tensorHom_id, rightKanEndAction_comp]
  rw [braiding_inv_naturality_left_assoc]
  rw [braiding_tensor_left_inv, braiding_tensor_right_inv]
  let E : V := rightKanEndObject u X b
  let R : V := b ⟶[V] c
  let S : V := c ⟶[V] d
  have hBraid :
      (α_ E R S).inv ≫
          ((β_ R E).inv ▷ S) ≫
          (α_ R E S).hom ≫
          (R ◁ (β_ S E).inv) ≫
          (α_ R S E).inv ≫
          ((β_ S R).inv ⊗ₘ 𝟙 E) ≫
          (α_ S R E).hom =
        (E ◁ (β_ S R).inv) ≫
          (α_ E S R).inv ≫
          ((β_ S E).inv ▷ R) ≫
          (α_ S E R).hom ≫
          (S ◁ (β_ R E).inv) := by
    have hy := congrArg (fun i => i.inv) (yang_baxter_iso S R E)
    simpa only [Iso.trans_inv, Iso.symm_inv,
      whiskerRightIso, whiskerLeftIso, tensorHom_id,
      Category.assoc] using hy
  have h := congrArg
    (fun q => q ≫
      (S ◁ rightKanEndAction u X b c) ≫
      rightKanEndAction u X c d) hBraid
  simpa only [E, R, S, MonoidalCategory.whiskerLeft_comp,
    Category.assoc, Iso.inv_hom_id_assoc] using h

/-- The enriched end map has the literal parameter-action formula on every
weighted-end projection. -/
@[reassoc]
public theorem rightKanEndMap_π (b c : B) (a : A) :
    MonoidalClosed.uncurry (rightKanEndMap u X b c) ≫
        π (rightKanWeight u c) X a =
      (β_ (b ⟶[V] c) (rightKanEndObject u X b)).inv ≫
        rightKanActionComponent u X b c a := by
  rw [rightKanEndMap_uncurry, Category.assoc,
    rightKanEndAction_π]

/-- The pointwise internal-Hom weighted ends, with their full parameter
action, form a genuine enriched functor on the target index.  This is the
object-and-map construction used by right enriched Kan extension; no Kan
counit or universal adjunction is asserted here. -/
public def rightKanEndFunctor : EnrichedFunctor V B V where
  obj b := rightKanEndObject u X b
  map b c := rightKanEndMap u X b c
  map_id b := rightKanEndMap_id u X b
  map_comp b c d := rightKanEndMap_comp u X b c d

/-- The right-Kan end functor uses the selected weighted end at every object. -/
@[simp]
public theorem rightKanEndFunctor_obj (b : B) :
    (rightKanEndFunctor u X).obj b = rightKanEndObject u X b := rfl

/-- The right-Kan end functor uses the full enriched parameter map above. -/
@[simp]
public theorem rightKanEndFunctor_map (b c : B) :
    (rightKanEndFunctor u X).map b c = rightKanEndMap u X b c := rfl

end RightKanEnd

private def yonedaEvaluation (c : I) (F : EnrichedFunctor V I V)
    [HasProduct (weightedEndObjects (covariantRepresentable c) F)]
    [HasProduct (weightedEndRelations (covariantRepresentable c) F)]
    [HasEqualizer (weightedEndLeft (covariantRepresentable c) F)
      (weightedEndRight (covariantRepresentable c) F)] :
    weightedEnd (covariantRepresentable c) F ⟶ F.obj c :=
  π (covariantRepresentable c) F c ≫
    (λ_ ((ihom (c ⟶[V] c)).obj (F.obj c))).inv ≫
    eId V c ▷ (ihom (c ⟶[V] c)).obj (F.obj c) ≫
    (ihom.ev (c ⟶[V] c)).app (F.obj c)

private def yonedaCoevaluation (c : I) (F : EnrichedFunctor V I V)
    [HasProduct (weightedEndObjects (covariantRepresentable c) F)]
    [HasProduct (weightedEndRelations (covariantRepresentable c) F)]
    [HasEqualizer (weightedEndLeft (covariantRepresentable c) F)
      (weightedEndRight (covariantRepresentable c) F)] :
    F.obj c ⟶ weightedEnd (covariantRepresentable c) F :=
  lift (covariantRepresentable c) F
    (yonedaComponent c F) (yonedaComponent_condition c F)

@[simp, reassoc]
private theorem yonedaCoevaluation_π (c : I)
    (F : EnrichedFunctor V I V)
    [HasProduct (weightedEndObjects (covariantRepresentable c) F)]
    [HasProduct (weightedEndRelations (covariantRepresentable c) F)]
    [HasEqualizer (weightedEndLeft (covariantRepresentable c) F)
      (weightedEndRight (covariantRepresentable c) F)] (a : I) :
    yonedaCoevaluation c F ≫ π (covariantRepresentable c) F a =
      yonedaComponent c F a := by
  simp [yonedaCoevaluation]

private theorem yonedaCoevaluation_evaluation (c : I)
    (F : EnrichedFunctor V I V)
    [HasProduct (weightedEndObjects (covariantRepresentable c) F)]
    [HasProduct (weightedEndRelations (covariantRepresentable c) F)]
    [HasEqualizer (weightedEndLeft (covariantRepresentable c) F)
      (weightedEndRight (covariantRepresentable c) F)] :
    yonedaCoevaluation c F ≫ yonedaEvaluation c F = 𝟙 (F.obj c) := by
  unfold yonedaEvaluation
  rw [← Category.assoc, yonedaCoevaluation_π]
  unfold yonedaComponent
  rw [MonoidalCategory.leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  have hm := F.map_id c
  have hu := congrArg MonoidalClosed.uncurry hm
  simp only [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.enrichedCategorySelf_id,
    MonoidalClosed.id_eq,
    MonoidalClosed.uncurry_curry] at hu
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [leftUnitor_inv_braiding_assoc]
  rw [hu]
  simp

private theorem yonedaEvaluation_coevaluation (c : I)
    (F : EnrichedFunctor V I V)
    [HasProduct (weightedEndObjects (covariantRepresentable c) F)]
    [HasProduct (weightedEndRelations (covariantRepresentable c) F)]
    [HasEqualizer (weightedEndLeft (covariantRepresentable c) F)
      (weightedEndRight (covariantRepresentable c) F)] :
    yonedaEvaluation c F ≫ yonedaCoevaluation c F =
      𝟙 (weightedEnd (covariantRepresentable c) F) := by
  apply hom_ext
  intro a
  rw [Category.assoc, yonedaCoevaluation_π, Category.id_comp]
  unfold yonedaEvaluation yonedaComponent
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  have hc := congrArg MonoidalClosed.uncurry
    (condition (covariantRepresentable c) F c a)
  simp only [MonoidalClosed.uncurry_curry] at hc
  dsimp [covariantRepresentable] at hc
  have heval :
      (λ_ (weightedEnd (covariantRepresentable c) F)).inv ≫
          eId V c ▷ weightedEnd (covariantRepresentable c) F ≫
          MonoidalClosed.uncurry
            (π (covariantRepresentable c) F c) =
        π (covariantRepresentable c) F c ≫
          (λ_ ((ihom (c ⟶[V] c)).obj (F.obj c))).inv ≫
          eId V c ▷ (ihom (c ⟶[V] c)).obj (F.obj c) ≫
          (ihom.ev (c ⟶[V] c)).app (F.obj c) := by
    rw [MonoidalClosed.uncurry_eq,
      MonoidalCategory.leftUnitor_inv_naturality_assoc,
      whisker_exchange_assoc]
  rw [← heval]
  let s : ((c ⟶[V] a) ⊗
        weightedEnd (covariantRepresentable c) F) ⟶
      (((c ⟶[V] a) ⊗ (c ⟶[V] c)) ⊗
        weightedEnd (covariantRepresentable c) F) :=
    ((c ⟶[V] a) ◁
        (λ_ (weightedEnd (covariantRepresentable c) F)).inv) ≫
      ((c ⟶[V] a) ◁
        (eId V c ▷ weightedEnd (covariantRepresentable c) F)) ≫
      (α_ (c ⟶[V] a) (c ⟶[V] c)
        (weightedEnd (covariantRepresentable c) F)).inv
  have hs := congrArg (fun k => s ≫ k) hc
  calc
    _ = s ≫
        ((α_ (c ⟶[V] a) (c ⟶[V] c)
              (weightedEnd (covariantRepresentable c) F)).hom ≫
          (c ⟶[V] a) ◁
              (c ⟶[V] c) ◁
                π (covariantRepresentable c) F c ≫
          (c ⟶[V] a) ◁
              (ihom.ev (c ⟶[V] c)).app (F.obj c) ≫
          (β_ (c ⟶[V] a) (F.obj c)).hom ≫
              MonoidalClosed.uncurry (F.map c a)) := by
            dsimp [s, covariantRepresentable]
            simp only [MonoidalCategory.whiskerLeft_comp,
              MonoidalClosed.uncurry_eq, Category.assoc,
              Iso.inv_hom_id_assoc]
    _ = s ≫
        ((((β_ (c ⟶[V] a) (c ⟶[V] c)).hom ≫
              eComp V c c a) ⊗ₘ
            𝟙 (weightedEnd (covariantRepresentable c) F)) ≫
          (c ⟶[V] a) ◁ π (covariantRepresentable c) F a ≫
          (ihom.ev (c ⟶[V] a)).app (F.obj a)) := hs
    _ = _ := by
      have hunit :
          (ρ_ (c ⟶[V] a)).inv ≫
              (c ⟶[V] a) ◁ eId V c ≫
              (β_ (c ⟶[V] a) (c ⟶[V] c)).hom ≫
              eComp V c c a = 𝟙 (c ⟶[V] a) := by
        rw [BraidedCategory.braiding_naturality_right_assoc]
        rw [rightUnitor_inv_braiding_assoc]
        exact e_id_comp V c a
      have hFactor :
          s ≫
              (((β_ (c ⟶[V] a) (c ⟶[V] c)).hom ≫
                    eComp V c c a) ⊗ₘ
                𝟙 (weightedEnd (covariantRepresentable c) F)) =
            (((ρ_ (c ⟶[V] a)).inv ≫
                  (c ⟶[V] a) ◁ eId V c ≫
                  (β_ (c ⟶[V] a) (c ⟶[V] c)).hom ≫
                  eComp V c c a) ⊗ₘ
              𝟙 (weightedEnd (covariantRepresentable c) F)) := by
        dsimp [s]
        monoidal
      rw [← Category.assoc, hFactor, hunit]
      simp only [MonoidalCategory.id_tensorHom_id,
        Category.id_comp, MonoidalClosed.uncurry_eq]

/-- The enriched end-Yoneda isomorphism, with evaluation at the enriched
identity as its forward map. -/
@[no_expose]
public def yonedaIso (c : I) (F : EnrichedFunctor V I V)
    :
    let R : EnrichedFunctor V I V :=
      { obj := fun a => c ⟶[V] a
        map := fun a b => MonoidalClosed.curry (eComp V c a b)
        map_id := (EnrichedFunctor.covariantRepresentable V I c).map_id
        map_comp := (EnrichedFunctor.covariantRepresentable V I c).map_comp }
    let t : I → V := fun a ↦ (ihom (R.obj a)).obj (F.obj a)
    let s : I × I → V := fun p ↦
      (ihom ((p.1 ⟶[V] p.2) ⊗ R.obj p.1)).obj (F.obj p.2)
    let l [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (α_ (p.1 ⟶[V] p.2) (R.obj p.1) (∏ᶜ t)).hom ≫
          ((p.1 ⟶[V] p.2) ◁ ((R.obj p.1) ◁ Pi.π t p.1)) ≫
          ((p.1 ⟶[V] p.2) ◁
            (ihom.ev (R.obj p.1)).app (F.obj p.1)) ≫
          (β_ (p.1 ⟶[V] p.2) (F.obj p.1)).hom ≫
          MonoidalClosed.uncurry (F.map p.1 p.2)
    let r [HasProduct t] [HasProduct s] : (∏ᶜ t) ⟶ ∏ᶜ s :=
      Pi.lift fun p ↦ MonoidalClosed.curry <|
        (((β_ (p.1 ⟶[V] p.2) (R.obj p.1)).hom ≫
            MonoidalClosed.uncurry (R.map p.1 p.2)) ⊗ₘ 𝟙 (∏ᶜ t)) ≫
          ((R.obj p.2) ◁ Pi.π t p.2) ≫
          (ihom.ev (R.obj p.2)).app (F.obj p.2)
    ∀ [HasProduct t] [HasProduct s] [HasEqualizer l r],
      equalizer l r ≅ F.obj c := by
  dsimp only
  intro _ _ _
  change weightedEnd (covariantRepresentable c) F ≅ F.obj c
  exact
    { hom := yonedaEvaluation c F
      inv := yonedaCoevaluation c F
      hom_inv_id := yonedaEvaluation_coevaluation c F
      inv_hom_id := yonedaCoevaluation_evaluation c F }

end weightedEnd

end CategoryTheory.Enriched
