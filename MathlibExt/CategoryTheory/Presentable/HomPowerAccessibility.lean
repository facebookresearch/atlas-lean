/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Presentable.AccessibleAdjunction
public import MathlibExt.CategoryTheory.Presentable.Completeness
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.CategoryTheory.Presentable.Limits
public import Mathlib.CategoryTheory.Comma.CardinalArrow
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Accessibility and common ranks of the original Hom-power functors

The functors are the literal native cofree/evaluation values returned by
original coefficient completeness. Their accessibility follows from the
actual original evaluation adjunction. A small representative family supplies
a common regular rank; original object labels are restored by explicit
unit-induced product reindexing isomorphisms.

No right-accessibility, power-accessibility or product dictionary is supplied
as a premise. Original labels and both comparison functions remain visible.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe w uM vM uD vD

namespace CategoryTheory.Presentable.HomPowerAccessibility

open Limits Opposite

variable (M : Type uM) [Category.{vM} M] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalLocallyPresentable M κ]
  {D : Type uD} [Category.{vD} D] {S : Type w} [SmallCategory S] (s : D ≌ S)

include κ in
/-- Coefficient pullbacks are internally derived from the admitted working-size completeness. -/
theorem hasPullbacks : HasPullbacks M :=
  Completeness.hasLimitsOfShape M κ WalkingCospan

include s in
/-- For κ-locally presentable `M` at regular κ and a supplied equivalence
`s : D ≌ S` to a small category `S`, the original ordinary diagram category
`D ⥤ M` is κ-locally presentable at that same rank. -/
theorem diagramLocallyPresentable : IsCardinalLocallyPresentable (D ⥤ M) κ := by
  let : HasPullbacks M := hasPullbacks M κ
  let : EssentiallySmall.{w} D := EssentiallySmall.mk' s
  infer_instance

/-- The SAME native cofree functor is accessible by its actual original evaluation adjunction. -/
theorem cofree_isAccessible (d : D) : Functor.IsAccessible.{w} (Completeness.cofree M κ s d) := by
  let : IsCardinalLocallyPresentable (D ⥤ M) κ := diagramLocallyPresentable M κ s
  let : IsAccessibleCategory.{w} (D ⥤ M) := ⟨κ, inferInstance, inferInstance⟩
  let : IsAccessibleCategory.{w} M := ⟨κ, inferInstance, inferInstance⟩
  exact AccessibleAdjunction.right_isAccessible_of_accessible
    (Completeness.evaluationCofreeAdjunction M κ s d)

include κ in
/-- Original evaluation preserves all working-size colimits, with no index-cardinality bound. -/
theorem evaluation_preservesColimits (e : D) :
    PreservesColimitsOfSize.{w, w} ((evaluation D M).obj e) where
  preservesColimitsOfShape {J} _ := by
    let : HasColimitsOfShape J M := inferInstance
    infer_instance

/-- Each original evaluation is accessible at the supplied regular cardinal. -/
theorem evaluation_isCardinalAccessible (e : D) :
    ((evaluation D M).obj e).IsCardinalAccessible κ := by
  let : PreservesColimitsOfSize.{w, w} ((evaluation D M).obj e) :=
    evaluation_preservesColimits M κ (D := D) e
  infer_instance

/-- Accessibility is proved for the literal original Hom-power functor. -/
theorem homPower_isAccessible (d e : D) :
    Functor.IsAccessible.{w} (Completeness.homPower M κ s d e) := by
  let : Functor.IsAccessible.{w} (Completeness.cofree M κ s d) := cofree_isAccessible M κ s d
  let : ((evaluation D M).obj e).IsCardinalAccessible κ := evaluation_isCardinalAccessible M κ e
  let : Functor.IsAccessible.{w} ((evaluation D M).obj e) :=
    Functor.isAccessible_of_isCardinalAccessible _ κ
  exact inferInstanceAs (Functor.IsAccessible.{w}
    (Completeness.cofree M κ s d ⋙ (evaluation D M).obj e))

section NativeCopowers

include κ s in
/-- Original Hom coproducts follow from coefficient colimits and actual index local smallness. -/
theorem homCoproducts (d e : D) : HasCoproductsOfShape (d ⟶ e) M := by
  let : LocallySmall.{w} D := locallySmall_of_faithful s.functor
  exact hasCoproductsOfShape_of_small (C := M) (d ⟶ e)

/-- The original free value is the native left adjoint of evaluation with internally derived
coproduct dictionaries. It retains every original Hom label. -/
def free (e : D) : M ⥤ D ⥤ M := by
  letI (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
  exact evaluationLeftAdjoint M e

/-- This is the SAME native free/evaluation adjunction, rather than a new chosen adjoint. -/
def freeEvaluationAdjunction (e : D) : free M κ s e ⊣ (evaluation D M).obj e := by
  letI (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
  exact evaluationAdjunctionRight M e

/-- The actual Hom copower uses native free followed by original evaluation. -/
def homCopower (d e : D) : M ⥤ M := free M κ s e ⋙ (evaluation D M).obj d

/-- The full copower value uses exactly the original Hom labels from e to d. -/
theorem homCopower_obj (d e : D) (X : M) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    (homCopower M κ s d e).obj X = ∐ fun _ : e ⟶ d ↦ X := rfl

/-- The whole copower map retains the actual coefficient map on every original summand. -/
theorem homCopower_map (d e : D) {X Y : M} (a : X ⟶ Y) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    (homCopower M κ s d e).map a =
      Sigma.desc (fun h : e ⟶ d ↦ a ≫ Sigma.ι (fun _ : e ⟶ d ↦ Y) h) := rfl

/-- Original free index action retains literal composition of the Hom label. -/
theorem free_index_map_ι (e : D) {d d' : D} (a : d ⟶ d') (X : M) (h : e ⟶ d) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    let _ : HasCoproductsOfShape (e ⟶ d') M := homCoproducts M κ s e d'
    Sigma.ι (fun _ : e ⟶ d ↦ X) h ≫ ((free M κ s e).obj X).map a =
      Sigma.ι (fun _ : e ⟶ d' ↦ X) (h ≫ a) := by
  let (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
  change Sigma.ι _ h ≫ Sigma.desc (fun g : e ⟶ d ↦
    Sigma.ι (fun _ : e ⟶ d' ↦ X) (g ≫ a)) = _
  exact Sigma.ι_comp_desc _ _

/-- The complete forward free transpose uses the ORIGINAL identity-labelled summand. -/
theorem free_homEquiv (e : D) (X : M) (F : D ⥤ M) (a : (free M κ s e).obj X ⟶ F) :
    let _ : HasCoproductsOfShape (e ⟶ e) M := homCoproducts M κ s e e
    (freeEvaluationAdjunction M κ s e).homEquiv X F a =
      Sigma.ι (fun _ : e ⟶ e ↦ X) (𝟙 e) ≫ a.app e := by
  let (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
  let a' : (evaluationLeftAdjoint M e).obj X ⟶ F := a
  change (evaluationAdjunctionRight M e).homEquiv X F a' = _
  rw [evaluationAdjunctionRight, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The complete inverse free transpose retains every original index-action map. -/
theorem free_homEquiv_symm_app (e d : D) (X : M) (F : D ⥤ M) (a : X ⟶ F.obj e) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    (((freeEvaluationAdjunction M κ s e).homEquiv X F).symm a).app d =
      Sigma.desc (fun h : e ⟶ d ↦ a ≫ F.map h) := by
  let (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
  change (((evaluationAdjunctionRight M e).homEquiv X F).symm a).app d = _
  rw [evaluationAdjunctionRight, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- Composition of the two actual evaluation adjunctions gives the adjunction to the
SAME original Hom-power functor. No const/limit adjoint is reselected. -/
def homCopowerPowerAdjunction (d e : D) :
    homCopower M κ s d e ⊣ Completeness.homPower M κ s d e :=
  (freeEvaluationAdjunction M κ s e).comp (Completeness.evaluationCofreeAdjunction M κ s d)

/-- The full Hom equivalence is literally the composition of the original two transposes. -/
theorem homCopowerPower_homEquiv (d e : D) (X Y : M) :
    (homCopowerPowerAdjunction M κ s d e).homEquiv X Y =
      ((Completeness.evaluationCofreeAdjunction M κ s d).homEquiv
        ((free M κ s e).obj X) Y).trans
      ((freeEvaluationAdjunction M κ s e).homEquiv X
        ((Completeness.cofree M κ s d).obj Y)) :=
  congrFun (congrFun (Adjunction.comp_homEquiv _ _) X) Y

/-- The whole forward Hom-power transpose is the original summand-to-projection map. -/
theorem homCopowerPower_homEquiv_apply (d e : D) {X Y : M}
    (f : (homCopower M κ s d e).obj X ⟶ Y) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    (homCopowerPowerAdjunction M κ s d e).homEquiv X Y f =
      Pi.lift (fun h : e ⟶ d ↦ Sigma.ι (fun _ : e ⟶ d ↦ X) h ≫ f) := by
  let (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
  let (a b : D) : HasProductsOfShape (a ⟶ b) M := Completeness.homProducts M κ s a b
  let f₀ : (∐ fun _ : e ⟶ d ↦ X) ⟶ Y := f
  let α := (Completeness.evaluationCofreeAdjunction M κ s d).homEquiv
    ((free M κ s e).obj X) Y f₀
  let a : X ⟶ ∏ᶜ fun _ : e ⟶ d ↦ Y :=
    (homCopowerPowerAdjunction M κ s d e).homEquiv X Y f₀
  let j : X ⟶ ∐ fun _ : e ⟶ e ↦ X := Sigma.ι (fun _ : e ⟶ e ↦ X) (𝟙 e)
  let b : (∐ fun _ : e ⟶ e ↦ X) ⟶ ∏ᶜ fun _ : e ⟶ d ↦ Y := α.app e
  have ha : a = j ≫ b := by
    change (homCopowerPowerAdjunction M κ s d e).homEquiv X Y f₀ = _
    rw [homCopowerPower_homEquiv]
    exact free_homEquiv M κ s e X ((Completeness.cofree M κ s d).obj Y) α
  change a = Pi.lift (fun h : e ⟶ d ↦ Sigma.ι (fun _ : e ⟶ d ↦ X) h ≫ f₀)
  apply Pi.hom_ext a _
  intro h
  let m : (∐ fun _ : e ⟶ e ↦ X) ⟶ ∐ fun _ : e ⟶ d ↦ X :=
    ((free M κ s e).obj X).map h
  have hb : b ≫ Pi.π (fun _ : e ⟶ d ↦ Y) h = m ≫ f₀ := by
    have hα : b = Pi.lift (fun h : e ⟶ d ↦
        ((free M κ s e).obj X).map h ≫ f₀) :=
      Completeness.cofree_homEquiv_app M κ s d e ((free M κ s e).obj X) Y f₀
    rw [hα]
    exact Pi.lift_comp_π _ _
  have hj : j ≫ m = Sigma.ι (fun _ : e ⟶ d ↦ X) h := by
    have hi : j ≫ m = Sigma.ι (fun _ : e ⟶ d ↦ X) (𝟙 e ≫ h) :=
      free_index_map_ι M κ s e h X (𝟙 e)
    simpa only [Category.id_comp] using hi
  rw [Pi.lift_comp_π, ha, Category.assoc, hb, ← Category.assoc, hj]

/-- The whole inverse transpose retains the original product projection at each summand. -/
theorem homCopowerPower_homEquiv_symm_apply (d e : D) {X Y : M}
    (f : X ⟶ (Completeness.homPower M κ s d e).obj Y) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    ((homCopowerPowerAdjunction M κ s d e).homEquiv X Y).symm f =
      Sigma.desc (fun h : e ⟶ d ↦ f ≫ Pi.π (fun _ : e ⟶ d ↦ Y) h) := by
  let (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
  let (a b : D) : HasProductsOfShape (a ⟶ b) M := Completeness.homProducts M κ s a b
  let f₀ : X ⟶ ∏ᶜ fun _ : e ⟶ d ↦ Y := f
  let α := ((freeEvaluationAdjunction M κ s e).homEquiv X
    ((Completeness.cofree M κ s d).obj Y)).symm f₀
  let a : (∐ fun _ : e ⟶ d ↦ X) ⟶ Y :=
    ((homCopowerPowerAdjunction M κ s d e).homEquiv X Y).symm f₀
  let b : (∐ fun _ : e ⟶ d ↦ X) ⟶ ∏ᶜ fun _ : d ⟶ d ↦ Y := α.app d
  let p : (∏ᶜ fun _ : d ⟶ d ↦ Y) ⟶ Y := Pi.π _ (𝟙 d)
  have ha : a = b ≫ p := by
    change ((homCopowerPowerAdjunction M κ s d e).homEquiv X Y).symm f₀ = _
    rw [homCopowerPower_homEquiv]
    exact Completeness.cofree_homEquiv_symm M κ s d ((free M κ s e).obj X) Y α
  change a = Sigma.desc (fun h : e ⟶ d ↦ f₀ ≫ Pi.π (fun _ : e ⟶ d ↦ Y) h)
  apply Sigma.hom_ext a _
  intro h
  let m : (∏ᶜ fun _ : e ⟶ d ↦ Y) ⟶ ∏ᶜ fun _ : d ⟶ d ↦ Y :=
    ((Completeness.cofree M κ s d).obj Y).map h
  have hb : Sigma.ι (fun _ : e ⟶ d ↦ X) h ≫ b = f₀ ≫ m := by
    have hα : b = Sigma.desc (fun h : e ⟶ d ↦
        f₀ ≫ ((Completeness.cofree M κ s d).obj Y).map h) :=
      free_homEquiv_symm_app M κ s e d X ((Completeness.cofree M κ s d).obj Y) f₀
    rw [hα]
    exact Sigma.ι_comp_desc _ _
  have hp : m ≫ p = Pi.π (fun _ : e ⟶ d ↦ Y) h := by
    have hi : m ≫ p = Pi.π (fun _ : e ⟶ d ↦ Y) (h ≫ 𝟙 d) :=
      Completeness.cofree_map_π M κ s d h Y (𝟙 d)
    simpa only [Category.comp_id] using hi
  rw [Sigma.ι_comp_desc, ha, ← Category.assoc, hb, Category.assoc, hp]


/-- Every projection of the actual composite unit is the original coproduct injection. -/
theorem homCopowerPower_unit_π (d e : D) (X : M) (h : e ⟶ d) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    (homCopowerPowerAdjunction M κ s d e).unit.app X ≫
        Pi.π (fun _ : e ⟶ d ↦ (homCopower M κ s d e).obj X) h =
      Sigma.ι (fun _ : e ⟶ d ↦ X) h := by
  let (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
  let (a b : D) : HasProductsOfShape (a ⟶ b) M := Completeness.homProducts M κ s a b
  let Y : M := ∐ fun _ : e ⟶ d ↦ X
  let u : X ⟶ ∏ᶜ fun _ : e ⟶ d ↦ Y :=
    (homCopowerPowerAdjunction M κ s d e).unit.app X
  have hu : u = (homCopowerPowerAdjunction M κ s d e).homEquiv X Y (𝟙 Y) := by
    have hn : (homCopowerPowerAdjunction M κ s d e).homEquiv X
        ((homCopower M κ s d e).obj X) (𝟙 _) =
        (homCopowerPowerAdjunction M κ s d e).unit.app X := by
      rw [Adjunction.homEquiv_unit]
      simp only [Functor.map_id]
      change u ≫ 𝟙 _ = u
      exact Category.comp_id u
    exact hn.symm
  have hv : u = Pi.lift (fun g : e ⟶ d ↦ Sigma.ι (fun _ : e ⟶ d ↦ X) g ≫ 𝟙 Y) :=
    hu.trans (homCopowerPower_homEquiv_apply M κ s d e (𝟙 Y))
  change u ≫ Pi.π (fun _ : e ⟶ d ↦ Y) h = _
  rw [hv, Pi.lift_comp_π, Category.comp_id]

/-- Every summand of the actual composite counit is the original product projection. -/
theorem homCopowerPower_counit_ι (d e : D) (Y : M) (h : e ⟶ d) :
    let _ : HasCoproductsOfShape (e ⟶ d) M := homCoproducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    Sigma.ι (fun _ : e ⟶ d ↦ (Completeness.homPower M κ s d e).obj Y) h ≫
        (homCopowerPowerAdjunction M κ s d e).counit.app Y =
      Pi.π (fun _ : e ⟶ d ↦ Y) h := by
  let (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
  let (a b : D) : HasProductsOfShape (a ⟶ b) M := Completeness.homProducts M κ s a b
  let X : M := ∏ᶜ fun _ : e ⟶ d ↦ Y
  let c : (∐ fun _ : e ⟶ d ↦ X) ⟶ Y :=
    (homCopowerPowerAdjunction M κ s d e).counit.app Y
  have hc : c = ((homCopowerPowerAdjunction M κ s d e).homEquiv X Y).symm (𝟙 X) := by
    have hn : ((homCopowerPowerAdjunction M κ s d e).homEquiv
        ((Completeness.homPower M κ s d e).obj Y) Y).symm (𝟙 _) =
        (homCopowerPowerAdjunction M κ s d e).counit.app Y := by
      rw [Adjunction.homEquiv_counit]
      simp only [Functor.map_id, Category.id_comp]
    exact hn.symm
  have hv : c = Sigma.desc (fun g : e ⟶ d ↦ 𝟙 X ≫ Pi.π (fun _ : e ⟶ d ↦ Y) g) :=
    hc.trans (homCopowerPower_homEquiv_symm_apply M κ s d e (𝟙 X))
  change Sigma.ι (fun _ : e ⟶ d ↦ X) h ≫ c = _
  rw [hv, Sigma.ι_comp_desc, Category.id_comp]


/-- A genuinely bounded original Hom coproduct of a presentable object is presentable,
using the actual native coproduct cocone and its actual injections. -/
theorem homCopower_presentable (d e : D) (μ : Cardinal.{w}) [Fact μ.IsRegular]
    (h : HasCardinalLT (e ⟶ d) μ) (X : M) [IsCardinalPresentable X μ] :
    IsCardinalPresentable ((homCopower M κ s d e).obj X) μ := by
  let (a b : D) : HasCoproductsOfShape (a ⟶ b) M := homCoproducts M κ s a b
  let : Small.{w} (e ⟶ d) := (locallySmall_of_faithful s.functor).hom_small e d
  let : HasLimitsOfShape (Discrete (e ⟶ d))ᵒᵖ (Type w) :=
    hasLimitsOfShape_of_essentiallySmall _ _
  let F := Discrete.functor (fun _ : e ⟶ d ↦ X)
  let (j : Discrete (e ⟶ d)) : IsCardinalPresentable (F.obj j) μ := by
    change IsCardinalPresentable X μ
    infer_instance
  change IsCardinalPresentable (colimit F) μ
  exact isCardinalPresentable_of_isColimit (colimit.cocone F) (colimit.isColimit F) μ
    ((hasCardinalLT_arrow_discrete_iff μ).2 h)

/-- Actual original Hom bounds give an enlarged regular accessibility rank for the SAME
Hom-power choice. Only the source generator compactness is enlarged. -/
theorem homPower_isCardinalAccessible_of_hom_bound (d e : D)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] (hκ : κ ≤ μ) (h : HasCardinalLT (e ⟶ d) μ) :
    (Completeness.homPower M κ s d e).IsCardinalAccessible μ :=
  AccessibleAdjunction.right_isCardinalAccessible_of_generator_images (κ := κ)
    (homCopowerPowerAdjunction M κ s d e) μ (fun t ↦ by
      let X := (AccessibleAdjunction.generator M κ).obj t
      let : IsCardinalPresentable X μ := isCardinalPresentable_of_le X hκ
      exact homCopower_presentable M κ s d e μ h X)

/-- The supplied cardinal is retained when its actual original Hom bound holds. -/
theorem homPower_isCardinalAccessible_fixed (d e : D) (h : HasCardinalLT (e ⟶ d) κ) :
    (Completeness.homPower M κ s d e).IsCardinalAccessible κ :=
  homPower_isCardinalAccessible_of_hom_bound M κ s d e κ le_rfl h

/-- Suppose `M` is κ-locally presentable at regular κ and `s : D ≌ S`
identifies the index with a small category. For regular μ with κ ≤ μ and
|Hom(e, d)| < μ for every original object `e`, the fixed cofree functor
`Completeness.cofree M κ s d` preserves μ-filtered colimits of working size
`(w, w)`. This is μ-accessibility, not preservation of all filtered colimits;
it follows by applying the same original Hom-power bounds componentwise. -/
theorem cofree_isCardinalAccessible_of_hom_bounds (d : D)
    (μ : Cardinal.{w}) [Fact μ.IsRegular] (hκ : κ ≤ μ)
    (h : ∀ e : D, HasCardinalLT (e ⟶ d) μ) :
    (Completeness.cofree M κ s d).IsCardinalAccessible μ := by
  refine ⟨fun J _ _ ↦ ?_⟩
  apply preservesColimitsOfShape_of_evaluation (Completeness.cofree M κ s d) J
  intro e
  let : (Completeness.homPower M κ s d e).IsCardinalAccessible μ :=
    homPower_isCardinalAccessible_of_hom_bound M κ s d e μ hκ (h e)
  exact Functor.preservesColimitsOfShape_of_isCardinalAccessible
    (Completeness.homPower M κ s d e) μ J

end NativeCopowers

section IndexIsomorphisms

variable {d d' : D} (i : d ≅ d')

/-- The original Hom-label equivalence is induced by the actual object isomorphism. -/
def homLabelEquiv (e : D) : (e ⟶ d) ≃ (e ⟶ d') := Iso.homCongr (Iso.refl e) i

/-- The complete forward label function is original postcomposition. -/
theorem homLabelEquiv_apply (e : D) (h : e ⟶ d) : homLabelEquiv i e h = h ≫ i.hom := by
  simp [homLabelEquiv, Iso.homCongr]

/-- The complete inverse label function is original inverse postcomposition. -/
theorem homLabelEquiv_symm_apply (e : D) (h : e ⟶ d') :
    (homLabelEquiv i e).symm h = h ≫ i.inv := by
  simp [homLabelEquiv, Iso.homCongr]

/-- Every coefficient component is the actual native reindexing of its original Hom product. -/
def componentIso (X : M) (e : D) :
    ((Completeness.cofree M κ s d).obj X).obj e ≅
      ((Completeness.cofree M κ s d').obj X).obj e := by
  letI (a b : D) : HasProductsOfShape (a ⟶ b) M := Completeness.homProducts M κ s a b
  exact Pi.reindex (homLabelEquiv i e) (fun _ : e ⟶ d' ↦ X)

/-- The forward comparison retains every ORIGINAL target Hom label. -/
theorem componentIso_hom_π (X : M) (e : D) (h : e ⟶ d') :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d') M := Completeness.homProducts M κ s e d'
    (componentIso M κ s i X e).hom ≫ Pi.π (fun _ : e ⟶ d' ↦ X) h =
      Pi.π (fun _ : e ⟶ d ↦ X) (h ≫ i.inv) := by
  let (a b : D) : HasProductsOfShape (a ⟶ b) M := Completeness.homProducts M κ s a b
  change (Pi.reindex (homLabelEquiv i e) (fun _ : e ⟶ d' ↦ X)).hom ≫
    Pi.π (fun _ : e ⟶ d' ↦ X) h = _
  have hi :
      (Pi.reindex (homLabelEquiv i e) (fun _ : e ⟶ d' ↦ X)).hom ≫
        Pi.π (fun _ : e ⟶ d' ↦ X) ((homLabelEquiv i e) ((homLabelEquiv i e).symm h)) =
          Pi.π (fun _ : e ⟶ d ↦ X) ((homLabelEquiv i e).symm h) :=
    Pi.reindex_hom_π (homLabelEquiv i e) (fun _ : e ⟶ d' ↦ X)
      ((homLabelEquiv i e).symm h)
  rw [Equiv.apply_symm_apply] at hi
  simpa only [homLabelEquiv_symm_apply] using hi

/-- The inverse comparison retains every ORIGINAL source Hom label. -/
theorem componentIso_inv_π (X : M) (e : D) (h : e ⟶ d) :
    let _ : HasProductsOfShape (e ⟶ d) M := Completeness.homProducts M κ s e d
    let _ : HasProductsOfShape (e ⟶ d') M := Completeness.homProducts M κ s e d'
    (componentIso M κ s i X e).inv ≫ Pi.π (fun _ : e ⟶ d ↦ X) h =
      Pi.π (fun _ : e ⟶ d' ↦ X) (h ≫ i.hom) := by
  let (a b : D) : HasProductsOfShape (a ⟶ b) M := Completeness.homProducts M κ s a b
  change (Pi.reindex (homLabelEquiv i e) (fun _ : e ⟶ d' ↦ X)).inv ≫
    Pi.π (fun _ : e ⟶ d ↦ X) h = _
  have hi :
      (Pi.reindex (homLabelEquiv i e) (fun _ : e ⟶ d' ↦ X)).inv ≫
        Pi.π (fun _ : e ⟶ d ↦ X) h =
          Pi.π (fun _ : e ⟶ d' ↦ X) ((homLabelEquiv i e) h) :=
    Pi.reindex_inv_π (homLabelEquiv i e) (fun _ : e ⟶ d' ↦ X) h
  simpa only [homLabelEquiv_apply] using hi

/-- The coefficient component comparisons are natural on every original index arrow. -/
theorem componentIso_naturality (X : M) {e f : D} (a : e ⟶ f) :
    ((Completeness.cofree M κ s d).obj X).map a ≫ (componentIso M κ s i X f).hom =
      (componentIso M κ s i X e).hom ≫ ((Completeness.cofree M κ s d').obj X).map a := by
  let (a b : D) : HasProductsOfShape (a ⟶ b) M := Completeness.homProducts M κ s a b
  let a₀ : (∏ᶜ fun _ : e ⟶ d ↦ X) ⟶ ∏ᶜ fun _ : f ⟶ d ↦ X :=
    ((Completeness.cofree M κ s d).obj X).map a
  let a₁ : (∏ᶜ fun _ : e ⟶ d' ↦ X) ⟶ ∏ᶜ fun _ : f ⟶ d' ↦ X :=
    ((Completeness.cofree M κ s d').obj X).map a
  let i₀ : (∏ᶜ fun _ : e ⟶ d ↦ X) ⟶ ∏ᶜ fun _ : e ⟶ d' ↦ X :=
    (componentIso M κ s i X e).hom
  let i₁ : (∏ᶜ fun _ : f ⟶ d ↦ X) ⟶ ∏ᶜ fun _ : f ⟶ d' ↦ X :=
    (componentIso M κ s i X f).hom
  change a₀ ≫ i₁ = i₀ ≫ a₁
  apply Pi.hom_ext (a₀ ≫ i₁) (i₀ ≫ a₁)
  intro h
  have hi₁ : i₁ ≫ Pi.π (fun _ : f ⟶ d' ↦ X) h =
      Pi.π (fun _ : f ⟶ d ↦ X) (h ≫ i.inv) := componentIso_hom_π M κ s i X f h
  have ha₀ : a₀ ≫ Pi.π (fun _ : f ⟶ d ↦ X) (h ≫ i.inv) =
      Pi.π (fun _ : e ⟶ d ↦ X) (a ≫ h ≫ i.inv) :=
    Completeness.cofree_map_π M κ s d a X (h ≫ i.inv)
  have ha₁ : a₁ ≫ Pi.π (fun _ : f ⟶ d' ↦ X) h =
      Pi.π (fun _ : e ⟶ d' ↦ X) (a ≫ h) :=
    Completeness.cofree_map_π M κ s d' a X h
  have hi₀ : i₀ ≫ Pi.π (fun _ : e ⟶ d' ↦ X) (a ≫ h) =
      Pi.π (fun _ : e ⟶ d ↦ X) ((a ≫ h) ≫ i.inv) :=
    componentIso_hom_π M κ s i X e (a ≫ h)
  rw [Category.assoc, hi₁, ha₀, Category.assoc, ha₁, hi₀]
  rw [Category.assoc]

/-- Reindexing preserves the full map for every original coefficient arrow. -/
theorem componentIso_coefficient_naturality {X Y : M} (a : X ⟶ Y) (e : D) :
    ((Completeness.cofree M κ s d).map a).app e ≫ (componentIso M κ s i Y e).hom =
      (componentIso M κ s i X e).hom ≫ ((Completeness.cofree M κ s d').map a).app e := by
  let (a b : D) : HasProductsOfShape (a ⟶ b) M := Completeness.homProducts M κ s a b
  let a₀ : (∏ᶜ fun _ : e ⟶ d ↦ X) ⟶ ∏ᶜ fun _ : e ⟶ d ↦ Y :=
    ((Completeness.cofree M κ s d).map a).app e
  let a₁ : (∏ᶜ fun _ : e ⟶ d' ↦ X) ⟶ ∏ᶜ fun _ : e ⟶ d' ↦ Y :=
    ((Completeness.cofree M κ s d').map a).app e
  let i₀ : (∏ᶜ fun _ : e ⟶ d ↦ X) ⟶ ∏ᶜ fun _ : e ⟶ d' ↦ X :=
    (componentIso M κ s i X e).hom
  let i₁ : (∏ᶜ fun _ : e ⟶ d ↦ Y) ⟶ ∏ᶜ fun _ : e ⟶ d' ↦ Y :=
    (componentIso M κ s i Y e).hom
  change a₀ ≫ i₁ = i₀ ≫ a₁
  apply Pi.hom_ext (a₀ ≫ i₁) (i₀ ≫ a₁)
  intro h
  have hi₁ : i₁ ≫ Pi.π (fun _ : e ⟶ d' ↦ Y) h =
      Pi.π (fun _ : e ⟶ d ↦ Y) (h ≫ i.inv) := componentIso_hom_π M κ s i Y e h
  have ha₀ : a₀ ≫ Pi.π (fun _ : e ⟶ d ↦ Y) (h ≫ i.inv) =
      Pi.π (fun _ : e ⟶ d ↦ X) (h ≫ i.inv) ≫ a :=
    Completeness.cofree_coefficient_map_π M κ s d e a (h ≫ i.inv)
  have ha₁ : a₁ ≫ Pi.π (fun _ : e ⟶ d' ↦ Y) h =
      Pi.π (fun _ : e ⟶ d' ↦ X) h ≫ a :=
    Completeness.cofree_coefficient_map_π M κ s d' e a h
  have hi₀ : i₀ ≫ Pi.π (fun _ : e ⟶ d' ↦ X) h =
      Pi.π (fun _ : e ⟶ d ↦ X) (h ≫ i.inv) := componentIso_hom_π M κ s i X e h
  rw [Category.assoc, hi₁, ha₀, Category.assoc, ha₁, ← Category.assoc, hi₀]

/-- The SAME actual cofree functors are naturally isomorphic under an original index Iso. -/
def cofreeIso : Completeness.cofree M κ s d ≅ Completeness.cofree M κ s d' :=
  NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (componentIso M κ s i X)
      (fun a ↦ componentIso_naturality M κ s i X a))
    (by
      intro X Y f
      ext e
      exact componentIso_coefficient_naturality M κ s i f e)

/-- The full forward cofree component is the actual product reindexing map. -/
theorem cofreeIso_hom_app (X : M) (e : D) :
    ((cofreeIso M κ s i).hom.app X).app e = (componentIso M κ s i X e).hom := rfl

/-- The full inverse cofree component is the actual inverse product reindexing map. -/
theorem cofreeIso_inv_app (X : M) (e : D) :
    ((cofreeIso M κ s i).inv.app X).app e = (componentIso M κ s i X e).inv := rfl

end IndexIsomorphisms

/-- Every original object is compared with the SAME chosen representative by the actual unit Iso. -/
def representativeIso (d : D) :
    Completeness.cofree M κ s d ≅
      Completeness.cofree M κ s (s.inverse.obj (s.functor.obj d)) :=
  cofreeIso M κ s (s.unitIso.app d)

/-- A genuine small representative family yields one compatible regular rank for EVERY
original cofree, evaluation and Hom-power functor. Accessibility and compact-object
preservation are both transported along actual original index isomorphisms. -/
theorem common_rank :
    ∃ (μ : Cardinal.{w}) (_ : Fact μ.IsRegular),
      IsCardinalAccessibleCategory M μ ∧ IsCardinalAccessibleCategory (D ⥤ M) μ ∧
      (∀ d : D, (Completeness.cofree M κ s d).IsCardinalAccessible μ) ∧
      (∀ d e : D, (Completeness.homPower M κ s d e).IsCardinalAccessible μ) ∧
      (∀ d : D, (Completeness.cofree M κ s d).PreservesCardinalPresentable μ) ∧
      (∀ e : D, ((evaluation D M).obj e).PreservesCardinalPresentable μ) ∧
        ∀ d e : D, (Completeness.homPower M κ s d e).PreservesCardinalPresentable μ := by
  let : IsCardinalLocallyPresentable (D ⥤ M) κ := diagramLocallyPresentable M κ s
  let : IsAccessibleCategory.{w} (D ⥤ M) := ⟨κ, inferInstance, inferInstance⟩
  let : IsAccessibleCategory.{w} M := ⟨κ, inferInstance, inferInstance⟩
  obtain ⟨μ, _, hC, hM, hR, _, hRP, hLP⟩ := AccessibleAdjunction.common_rank
    (fun t : S ↦ (evaluation D M).obj (s.inverse.obj t))
    (fun t : S ↦ Completeness.cofree M κ s (s.inverse.obj t))
    (fun t ↦ Completeness.evaluationCofreeAdjunction M κ s (s.inverse.obj t))
  let (t : S) : (Completeness.cofree M κ s
      (s.inverse.obj t)).IsCardinalAccessible μ := hR t
  let (t : S) : (Completeness.cofree M κ s
      (s.inverse.obj t)).PreservesCardinalPresentable μ := hRP t
  let (t : S) : ((evaluation D M).obj
      (s.inverse.obj t)).PreservesCardinalPresentable μ := hLP t
  have hOrig (d : D) : (Completeness.cofree M κ s d).IsCardinalAccessible μ :=
    Functor.isCardinalAccessible_of_natIso (representativeIso M κ s d).symm μ
  have hOrigP (d : D) : (Completeness.cofree M κ s d).PreservesCardinalPresentable μ :=
    Functor.PreservesCardinalPresentable.of_iso (representativeIso M κ s d).symm μ
  have hEvalP (e : D) : ((evaluation D M).obj e).PreservesCardinalPresentable μ := by
    let : ((evaluation D M).obj
        ((s.functor ⋙ s.inverse).obj e)).PreservesCardinalPresentable μ :=
      hLP (s.functor.obj e)
    exact Functor.PreservesCardinalPresentable.of_iso
      ((evaluation D M).mapIso (s.unitIso.app e)).symm μ
  refine ⟨μ, inferInstance, hM, hC, hOrig, ?_, hOrigP, hEvalP, ?_⟩
  · intro d e
    let : (Completeness.cofree M κ s d).IsCardinalAccessible μ := hOrig d
    let : PreservesColimitsOfSize.{w, w} ((evaluation D M).obj e) :=
      evaluation_preservesColimits M κ e
    let : ((evaluation D M).obj e).IsCardinalAccessible μ := inferInstance
    exact inferInstanceAs
      ((Completeness.cofree M κ s d ⋙ (evaluation D M).obj e).IsCardinalAccessible μ)
  · intro d e
    let : (Completeness.cofree M κ s d).PreservesCardinalPresentable μ := hOrigP d
    let : ((evaluation D M).obj e).PreservesCardinalPresentable μ := hEvalP e
    exact inferInstanceAs
      ((Completeness.cofree M κ s d ⋙ (evaluation D M).obj e).PreservesCardinalPresentable μ)


include s in
/-- An actual bound on the small representative arrow type bounds each ORIGINAL Hom type.
The faithful map and fixed-endpoint Arrow injection are retained explicitly. -/
theorem hom_bound_of_representative_arrows (μ : Cardinal.{w})
    (h : HasCardinalLT (Arrow S) μ) (d e : D) : HasCardinalLT (e ⟶ d) μ :=
  h.of_injective (fun f : e ⟶ d ↦ Arrow.mk (s.functor.map f))
    ((Arrow.mk_injective _ _).comp s.functor.map_injective)

/-- A structural representative-arrow bound proves accessibility at the SAME input cardinal
for all original cofree and Hom-power functors; no object-surjectivity is used. -/
theorem fixed_rank_of_representative_arrow_bound
    (h : HasCardinalLT (Arrow S) κ) :
    (∀ d : D, (Completeness.cofree M κ s d).IsCardinalAccessible κ) ∧
      ∀ d e : D, (Completeness.homPower M κ s d e).IsCardinalAccessible κ := by
  have hHom := hom_bound_of_representative_arrows s κ h
  exact ⟨fun d ↦ cofree_isCardinalAccessible_of_hom_bounds M κ s d κ le_rfl (hHom d),
    fun d e ↦ homPower_isCardinalAccessible_fixed M κ s d e (hHom d e)⟩

/-- The actual small representative arrow type internally supplies a compatible regular
rank above the supplied cardinal. All ORIGINAL objects, arrows and functor choices stay fixed. -/
theorem bounded_common_rank :
    ∃ (μ : Cardinal.{w}) (_ : Fact μ.IsRegular), κ ≤ μ ∧
      HasCardinalLT (Arrow S) μ ∧
      IsCardinalLocallyPresentable M μ ∧ IsCardinalLocallyPresentable (D ⥤ M) μ ∧
      (∀ d e : D, HasCardinalLT (e ⟶ d) μ) ∧
      (∀ d : D, (Completeness.cofree M κ s d).IsCardinalAccessible μ) ∧
        ∀ d e : D, (Completeness.homPower M κ s d e).IsCardinalAccessible μ := by
  obtain ⟨μ₀, hRegular, hArrow⟩ := HasCardinalLT.exists_regular_cardinal (Arrow S)
  let : Fact μ₀.IsRegular := ⟨hRegular⟩
  obtain ⟨μ, _, hκ, hμ₀⟩ := Cardinal.SharplyLT.exists_of_pair κ μ₀
  have hArrow' := hArrow.of_le hμ₀.le
  have hHom := hom_bound_of_representative_arrows s μ hArrow'
  let : IsCardinalLocallyPresentable (D ⥤ M) κ := diagramLocallyPresentable M κ s
  refine ⟨μ, inferInstance, hκ.le, hArrow',
    IsCardinalLocallyPresentable.of_le M hκ.le,
    IsCardinalLocallyPresentable.of_le (D ⥤ M) hκ.le, hHom, ?_, ?_⟩
  · exact fun d ↦ cofree_isCardinalAccessible_of_hom_bounds M κ s d μ hκ.le (hHom d)
  · exact fun d e ↦ homPower_isCardinalAccessible_of_hom_bound M κ s d e μ hκ.le (hHom d e)

end CategoryTheory.Presentable.HomPowerAccessibility
