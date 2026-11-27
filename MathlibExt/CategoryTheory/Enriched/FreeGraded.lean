/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeEvaluation
public import MathlibExt.CategoryTheory.Enriched.LeftKanGradedAction
public import Mathlib.CategoryTheory.Yoneda

/-!
# The original free/Lan generators in every central grade

The original cotensor and free Hom correspondences give the coefficient map.
All free and coend generator actions retain their original Hom parameters.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uA uB uV vV

open CategoryTheory Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.FreeGraded

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- The original free identity slot, before any Kan identity insertion. -/
def identityInsertion (a : A) (M : V) : M ⟶ M ⊗ (a ⟶[V] a) :=
  (ρ_ M).inv ≫ M ◁ eId V a

/-- Every actual central grade uses the original free and cotensor Hom functions. -/
@[no_expose]
def evaluationEquiv (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V A) :
    GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor ≃
      (Γ.1 ⊗ M ⟶ Y.toEnrichedFunctor.obj a) :=
  (gradedCotensorEquiv Γ (Free.object a M) Y).trans
    ((Free.homEquiv a M (cotensorObject Γ.1 Y)).trans
      ((ihom.adjunction Γ.1).homEquiv M (Y.toEnrichedFunctor.obj a)).symm)

/-- The complete forward coefficient map is the original identity evaluation. -/
private theorem evaluationEquiv_apply_private (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) :
    evaluationEquiv Γ a M Y t =
      MonoidalClosed.uncurry (Free.evaluate a M (cotensorObject Γ.1 Y)
        (gradedToCotensor Γ (Free.object a M) Y t)) := by
  change ((ihom.adjunction Γ.1).homEquiv M (Y.toEnrichedFunctor.obj a)).symm
    (Free.evaluate a M (cotensorObject Γ.1 Y)
      (gradedCotensorEquiv Γ (Free.object a M) Y t)) = _
  rw [MonoidalClosed.homEquiv_symm_apply_eq, gradedCotensorEquiv_apply]

/-- The complete forward coefficient map is the original identity evaluation. -/
theorem evaluationEquiv_apply (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) :
    evaluationEquiv Γ a M Y t =
      MonoidalClosed.uncurry (Free.evaluate a M (cotensorObject Γ.1 Y)
        (gradedToCotensor Γ (Free.object a M) Y t)) :=
  evaluationEquiv_apply_private Γ a M Y t

/-- The forward formula inserts the original free identity into the full graded component. -/
theorem evaluationEquiv_gradeFirst (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) :
    evaluationEquiv Γ a M Y t = (Γ.1 ◁ identityInsertion a M) ≫
      GradedNatTrans.gradeFirstComponent Γ t a := by
  rw [evaluationEquiv_apply, Free.evaluate, gradedToCotensor_component,
    ← Category.assoc, MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  rfl

/-- The inverse descends through the same full original free action. -/
private theorem evaluationEquiv_symm_apply_private (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (f : Γ.1 ⊗ M ⟶ Y.toEnrichedFunctor.obj a) :
    (evaluationEquiv Γ a M Y).symm f =
      cotensorToGraded Γ (Free.object a M) Y
        (Free.extend a M (cotensorObject Γ.1 Y) (MonoidalClosed.curry f)) := by
  change (gradedCotensorEquiv Γ (Free.object a M) Y).symm
    (Free.extend a M (cotensorObject Γ.1 Y)
      ((ihom.adjunction Γ.1).homEquiv M (Y.toEnrichedFunctor.obj a) f)) = _
  rw [MonoidalClosed.homEquiv_apply_eq, gradedCotensorEquiv_symm_apply]

/-- The inverse descends through the same full original free action. -/
theorem evaluationEquiv_symm_apply (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (f : Γ.1 ⊗ M ⟶ Y.toEnrichedFunctor.obj a) :
    (evaluationEquiv Γ a M Y).symm f =
      cotensorToGraded Γ (Free.object a M) Y
        (Free.extend a M (cotensorObject Γ.1 Y) (MonoidalClosed.curry f)) :=
  evaluationEquiv_symm_apply_private Γ a M Y f

/-- Every inverse free component keeps the entire original source Hom parameter. -/
theorem evaluationEquiv_symm_gradeFirst (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (f : Γ.1 ⊗ M ⟶ Y.toEnrichedFunctor.obj a) (b : A) :
    GradedNatTrans.gradeFirstComponent Γ ((evaluationEquiv Γ a M Y).symm f) b =
      (α_ Γ.1 M (a ⟶[V] b)).inv ≫ (f ▷ (a ⟶[V] b)) ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map a b) := by
  rw [evaluationEquiv_symm_apply, cotensorToGraded_gradeFirst]
  dsimp only [cotensorComponent]
  rw [Free.extend_component]
  dsimp only [Free.extensionComponent]
  rw [tensorHom_id, MonoidalClosed.uncurry_natural_left,
    EnrichedFunctor.cotensor_doubleUncurry,
    associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]

/-- The actual inverse component uses the supplied grade half-braiding. -/
theorem evaluationEquiv_symm_app (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (f : Γ.1 ⊗ M ⟶ Y.toEnrichedFunctor.obj a) (b : A) :
    ((evaluationEquiv Γ a M Y).symm f).app b =
      MonoidalClosed.curry ((Γ.2.β (M ⊗ (a ⟶[V] b))).inv ≫
        (α_ Γ.1 M (a ⟶[V] b)).inv ≫ (f ▷ (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map a b)) := by
  have h := evaluationEquiv_symm_gradeFirst Γ a M Y f b
  rw [evaluationEquiv_symm_apply, cotensorToGraded_gradeFirst] at h
  rw [evaluationEquiv_symm_apply, cotensorToGraded_app, h]

/-- Evaluation and extension are inverse on full graded transformations. -/
theorem evaluationEquiv_left_inverse (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) :
    (evaluationEquiv Γ a M Y).symm (evaluationEquiv Γ a M Y t) = t :=
  (evaluationEquiv Γ a M Y).symm_apply_apply t

/-- Extension and evaluation recover the actual supplied coefficient arrow. -/
theorem evaluationEquiv_right_inverse (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (f : Γ.1 ⊗ M ⟶ Y.toEnrichedFunctor.obj a) :
    evaluationEquiv Γ a M Y ((evaluationEquiv Γ a M Y).symm f) = f :=
  (evaluationEquiv Γ a M Y).apply_symm_apply f

/-- The raw coefficient Hom uses the actual grade half-braiding on the coefficient. -/
@[no_expose]
def homEquiv (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V A) :
    GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor ≃
      (Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) :=
  (evaluationEquiv Γ a M Y).trans
    ((Iso.homCongr (Γ.2.β M) (Iso.refl (Y.toEnrichedFunctor.obj a))).trans
      ((ihom.adjunction M).homEquiv Γ.1 (Y.toEnrichedFunctor.obj a)))

/-- Raw evaluation is currying after the actual inverse grade half-braiding. -/
private theorem homEquiv_factor_private (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) :
    homEquiv Γ a M Y t = MonoidalClosed.curry
      ((Γ.2.β M).inv ≫ evaluationEquiv Γ a M Y t) := by
  change MonoidalClosed.curry
    (Iso.homCongr (Γ.2.β M) (Iso.refl (Y.toEnrichedFunctor.obj a))
      (evaluationEquiv Γ a M Y t)) = _
  rw [Iso.homCongr_apply]
  change MonoidalClosed.curry
    ((Γ.2.β M).inv ≫ evaluationEquiv Γ a M Y t ≫ 𝟙 _) = _
  rw [Category.comp_id]

/-- Raw evaluation is currying after the actual inverse grade half-braiding. -/
theorem homEquiv_factor (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) :
    homEquiv Γ a M Y t = MonoidalClosed.curry
      ((Γ.2.β M).inv ≫ evaluationEquiv Γ a M Y t) :=
  homEquiv_factor_private Γ a M Y t

/-- The full raw coefficient image is precomposition by the original identity slot. -/
theorem homEquiv_apply (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) :
    homEquiv Γ a M Y t =
      t.app a ≫ (MonoidalClosed.pre (identityInsertion a M)).app (Y.toEnrichedFunctor.obj a) := by
  apply MonoidalClosed.uncurry_injective
  apply (cancel_epi (Γ.2.β M).hom).1
  rw [homEquiv_factor, MonoidalClosed.uncurry_curry, Iso.hom_inv_id_assoc,
    MonoidalClosed.uncurry_pre_app, evaluationEquiv_gradeFirst]
  change (Γ.1 ◁ identityInsertion a M) ≫ (Γ.2.β (M ⊗ (a ⟶[V] a))).hom ≫
      MonoidalClosed.uncurry (t.app a) = _
  exact HalfBraiding.naturality_assoc Γ.2 (identityInsertion a M)
    (MonoidalClosed.uncurry (t.app a))

/-- The raw inverse uses the same original grade-first coefficient map. -/
private theorem homEquiv_symm_factor_private (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) :
    (homEquiv Γ a M Y).symm f =
      (evaluationEquiv Γ a M Y).symm ((Γ.2.β M).hom ≫ MonoidalClosed.uncurry f) := by
  change (evaluationEquiv Γ a M Y).symm
    (Iso.homCongr (Γ.2.β M).symm (Iso.refl (Y.toEnrichedFunctor.obj a)).symm
      (MonoidalClosed.uncurry f)) = _
  rw [Iso.homCongr_apply]
  change (evaluationEquiv Γ a M Y).symm
    ((Γ.2.β M).hom ≫ MonoidalClosed.uncurry f ≫ 𝟙 _) = _
  rw [Category.comp_id]

/-- The raw inverse uses the same original grade-first coefficient map. -/
theorem homEquiv_symm_factor (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) :
    (homEquiv Γ a M Y).symm f =
      (evaluationEquiv Γ a M Y).symm ((Γ.2.β M).hom ≫ MonoidalClosed.uncurry f) :=
  homEquiv_symm_factor_private Γ a M Y f

/-- The raw inverse retains every original free Hom action. -/
theorem homEquiv_symm_gradeFirst (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) (b : A) :
    GradedNatTrans.gradeFirstComponent Γ ((homEquiv Γ a M Y).symm f) b =
      (α_ Γ.1 M (a ⟶[V] b)).inv ≫
        (((Γ.2.β M).hom ≫ MonoidalClosed.uncurry f) ▷ (a ⟶[V] b)) ≫
          MonoidalClosed.uncurry (Y.toEnrichedFunctor.map a b) := by
  rw [homEquiv_symm_factor, evaluationEquiv_symm_gradeFirst]

private theorem identityInsertion_coefficient {M N : V} (a : A) (f : M ⟶ N) :
    identityInsertion a M ≫ component (Free.coefficientMap a f) a =
      f ≫ identityInsertion a N := by
  rw [Free.coefficientMap_component]
  dsimp only [identityInsertion]
  rw [Category.assoc, whisker_exchange, ← Category.assoc,
    ← rightUnitor_inv_naturality, Category.assoc]

/-- Actual coefficient maps act by the original closed precomposition map. -/
theorem homEquiv_coefficient (Γ : Center V) (a : A) {M N : V} (f : M ⟶ N)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Γ (Free.object a N).toEnrichedFunctor Y.toEnrichedFunctor) :
    homEquiv Γ a M Y (gradedPrecomp Γ (Free.coefficientMap a f) t) =
      homEquiv Γ a N Y t ≫ (MonoidalClosed.pre f).app (Y.toEnrichedFunctor.obj a) := by
  rw [homEquiv_apply, gradedPrecomp_app, homEquiv_apply]
  have h₁ := congrArg (fun q => q.app (Y.toEnrichedFunctor.obj a))
    (MonoidalClosed.pre_map (identityInsertion a M) (component (Free.coefficientMap a f) a))
  have h₂ := congrArg (fun q => q.app (Y.toEnrichedFunctor.obj a))
    (MonoidalClosed.pre_map f (identityInsertion a N))
  have h₃ := congrArg (fun q => (MonoidalClosed.pre q).app (Y.toEnrichedFunctor.obj a))
    (identityInsertion_coefficient a f)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => t.app a ≫ q) h₁.symm).trans
      ((congrArg (fun q => t.app a ≫ q) h₃).trans
        ((congrArg (fun q => t.app a ≫ q) h₂).trans (Category.assoc _ _ _).symm)))

/-- Genuine target maps retain their entire original component under coefficient evaluation. -/
theorem homEquiv_postcomp (Γ : Center V) (a : A) (M : V)
    {Y Y' : EnrichedFunctorCat V A}
    (t : GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) (q : Y ⟶ Y') :
    homEquiv Γ a M Y' (gradedPostcomp Γ t q) =
      homEquiv Γ a M Y t ≫ (ihom M).map (component q a) := by
  rw [homEquiv_apply, gradedPostcomp_app, homEquiv_apply]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun p => t.app a ≫ p)
      ((MonoidalClosed.pre (identityInsertion a M)).naturality (component q a))).trans
        (Category.assoc _ _ _).symm)

/-- Every genuine central scalar map acts on the same original raw coefficient function. -/
theorem homEquiv_regrade {Γ Δ : Center V} (h : Γ ⟶ Δ) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Δ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) :
    homEquiv Γ a M Y (GradedNatTrans.regrade h t) = h.f ≫ homEquiv Δ a M Y t := by
  rw [homEquiv_apply, GradedNatTrans.regrade_app, homEquiv_apply, Category.assoc]

/-- Inverse coefficient naturality uses the same full original free map. -/
theorem homEquiv_symm_coefficient (Γ : Center V) (a : A) {M N : V} (f : M ⟶ N)
    (Y : EnrichedFunctorCat V A) (g : Γ.1 ⟶ (ihom N).obj (Y.toEnrichedFunctor.obj a)) :
    (homEquiv Γ a M Y).symm (g ≫ (MonoidalClosed.pre f).app (Y.toEnrichedFunctor.obj a)) =
      gradedPrecomp Γ (Free.coefficientMap a f) ((homEquiv Γ a N Y).symm g) := by
  apply (homEquiv Γ a M Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_coefficient, Equiv.apply_symm_apply]

/-- Inverse target naturality retains the genuine original target transformation. -/
theorem homEquiv_symm_postcomp (Γ : Center V) (a : A) (M : V)
    {Y Y' : EnrichedFunctorCat V A} (q : Y ⟶ Y')
    (g : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) :
    (homEquiv Γ a M Y').symm (g ≫ (ihom M).map (component q a)) =
      gradedPostcomp Γ ((homEquiv Γ a M Y).symm g) q := by
  apply (homEquiv Γ a M Y').injective
  rw [Equiv.apply_symm_apply, homEquiv_postcomp, Equiv.apply_symm_apply]

/-- Inverse central regrading is the same original scalar precomposition. -/
theorem homEquiv_symm_regrade {Γ Δ : Center V} (h : Γ ⟶ Δ) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (g : Δ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) :
    (homEquiv Γ a M Y).symm (h.f ≫ g) =
      GradedNatTrans.regrade h ((homEquiv Δ a M Y).symm g) := by
  apply (homEquiv Γ a M Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_regrade, Equiv.apply_symm_apply]

/-- Both complete original raw Hom functions are inverse. -/
theorem homEquiv_left_inverse (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A)
    (t : GradedNatTrans Γ (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor) :
    (homEquiv Γ a M Y).symm (homEquiv Γ a M Y t) = t :=
  (homEquiv Γ a M Y).symm_apply_apply t

/-- The original raw coefficient arrow is recovered exactly. -/
theorem homEquiv_right_inverse (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a)) :
    homEquiv Γ a M Y ((homEquiv Γ a M Y).symm f) = f :=
  (homEquiv Γ a M Y).apply_symm_apply f

/-- The full actual transformation presheaf acts by original scalar precomposition. -/
theorem homEquiv_presheaf_naturality (a : A) (M : V) (Y : EnrichedFunctorCat V A)
    {K L : Vᵒᵖ} (h : K ⟶ L)
    (t : (enrichedNatTransYoneda (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor).obj K) :
    homEquiv ((Center.ofBraided V).obj L.unop) a M Y
        ((enrichedNatTransYoneda (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor).map h t) =
      (yoneda.obj ((ihom M).obj (Y.toEnrichedFunctor.obj a))).map h
        (homEquiv ((Center.ofBraided V).obj K.unop) a M Y t) := by
  have h₁ := homEquiv_apply ((Center.ofBraided V).obj L.unop) a M Y
    ((enrichedNatTransYoneda (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor).map h t)
  have h₂ := homEquiv_apply ((Center.ofBraided V).obj K.unop) a M Y t
  have ht : ((enrichedNatTransYoneda (Free.object a M).toEnrichedFunctor
      Y.toEnrichedFunctor).map h t).app a = h.unop ≫ t.app a := rfl
  have hm : (yoneda.obj ((ihom M).obj (Y.toEnrichedFunctor.obj a))).map h
      (homEquiv ((Center.ofBraided V).obj K.unop) a M Y t) =
        h.unop ≫ homEquiv ((Center.ofBraided V).obj K.unop) a M Y t := rfl
  exact h₁.trans
    ((congrArg (fun p => p ≫
      (MonoidalClosed.pre (identityInsertion a M)).app (Y.toEnrichedFunctor.obj a)) ht).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun p => h.unop ≫ p) h₂.symm).trans hm.symm)))

/-- The actual enriched transformation presheaf is represented by the original coefficient Hom. -/
@[no_expose]
def enrichedNatTransYonedaIso (a : A) (M : V) (Y : EnrichedFunctorCat V A) :
    enrichedNatTransYoneda (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor ⋙
        uliftFunctor.{max uA vV, max uA vV} ≅
      yoneda.obj ((ihom M).obj (Y.toEnrichedFunctor.obj a)) ⋙
        uliftFunctor.{max uA vV, vV} :=
  NatIso.ofComponents
    (fun K => (Equiv.ulift.trans
      ((homEquiv ((Center.ofBraided V).obj K.unop) a M Y).trans Equiv.ulift.symm)).toIso)
    (by
      intro K L h
      apply ConcreteCategory.ext_apply
      intro t
      apply ULift.ext
      exact homEquiv_presheaf_naturality a M Y h t.down)

private theorem enrichedNatTransYonedaIso_hom_app_private (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (K : Vᵒᵖ)
    (t : ULift.{max uA vV}
      ((enrichedNatTransYoneda (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor).obj K)) :
    (enrichedNatTransYonedaIso a M Y).hom.app K t =
      ULift.up (homEquiv ((Center.ofBraided V).obj K.unop) a M Y t.down) := rfl

/-- Every coefficient of the actual lifted presheaf comparison uses original raw evaluation. -/
theorem enrichedNatTransYonedaIso_hom_app (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (K : Vᵒᵖ)
    (t : ULift.{max uA vV}
      ((enrichedNatTransYoneda (Free.object a M).toEnrichedFunctor Y.toEnrichedFunctor).obj K)) :
    (enrichedNatTransYonedaIso a M Y).hom.app K t =
      ULift.up (homEquiv ((Center.ofBraided V).obj K.unop) a M Y t.down) :=
  enrichedNatTransYonedaIso_hom_app_private a M Y K t

private theorem enrichedNatTransYonedaIso_inv_app_private (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (K : Vᵒᵖ)
    (t : ULift.{max uA vV} (K.unop ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a))) :
    (enrichedNatTransYonedaIso a M Y).inv.app K t =
      ULift.up ((homEquiv ((Center.ofBraided V).obj K.unop) a M Y).symm t.down) := rfl

/-- Every inverse presheaf coefficient is the original full graded free extension. -/
theorem enrichedNatTransYonedaIso_inv_app (a : A) (M : V)
    (Y : EnrichedFunctorCat V A) (K : Vᵒᵖ)
    (t : ULift.{max uA vV} (K.unop ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj a))) :
    (enrichedNatTransYonedaIso a M Y).inv.app K t =
      ULift.up ((homEquiv ((Center.ofBraided V).obj K.unop) a M Y).symm t.down) :=
  enrichedNatTransYonedaIso_inv_app_private a M Y K t

omit [BraidedCategory V] in
private theorem restriction_uncurry {B : Type uB} [EnrichedCategory V B]
    (j : EnrichedFunctor V A B) (Y : EnrichedFunctorCat V B) (a a' : A) :
    MonoidalClosed.uncurry ((restrictionObject j Y).toEnrichedFunctor.map a a') =
      (Y.toEnrichedFunctor.obj (j.obj a) ◁ j.map a a') ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) (j.obj a')) :=
  MonoidalClosed.uncurry_natural_left (j.map a a')
    (Y.toEnrichedFunctor.map (j.obj a) (j.obj a'))

/-- The original free/coend generator retains both full source Hom factors and index maps. -/
def lanGenerator {B : Type uB} [EnrichedCategory V B]
    (j : EnrichedFunctor V A B) (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) (b : B) (a' : A) :
    Γ.1 ⊗ ((j.obj a' ⟶[V] b) ⊗ (M ⊗ (a ⟶[V] a'))) ⟶ Y.toEnrichedFunctor.obj b :=
  (α_ Γ.1 (j.obj a' ⟶[V] b) (M ⊗ (a ⟶[V] a'))).inv ≫
    ((β_ (j.obj a' ⟶[V] b) Γ.1).inv ▷ (M ⊗ (a ⟶[V] a'))) ≫
    (α_ (j.obj a' ⟶[V] b) Γ.1 (M ⊗ (a ⟶[V] a'))).hom ≫
    ((j.obj a' ⟶[V] b) ◁
      ((α_ Γ.1 M (a ⟶[V] a')).inv ≫
        (((Γ.2.β M).hom ≫ MonoidalClosed.uncurry f) ▷ (a ⟶[V] a')) ≫
        (Y.toEnrichedFunctor.obj (j.obj a) ◁ j.map a a') ≫
        MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a) (j.obj a')))) ≫
    (β_ (j.obj a' ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a'))).hom ≫
    MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a') b)

section Lan
variable {B : Type uB} [EnrichedCategory V B] (j : EnrichedFunctor V A B)
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight j b) X.toEnrichedFunctor)]
  [∀ (X : EnrichedFunctorCat V A) (b : B),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight j b) X.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight j b) X.toEnrichedFunctor)]

/-- The complete all-grade free/Lan coefficient correspondence uses the original coends. -/
@[no_expose]
def lanHomEquiv (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B) :
    GradedNatTrans Γ (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor ≃ (Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :=
  (leftKanGradedHomEquiv j Γ (Free.object a M) Y).trans
    (homEquiv Γ a M (restrictionObject j Y))

/-- The coefficient image uses both original identity insertions. -/
theorem lanHomEquiv_apply (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor) :
    lanHomEquiv j Γ a M Y t = t.app (j.obj a) ≫
      (MonoidalClosed.pre (identityInsertion a M ≫ leftKanUnitComponent j (Free.object a M) a)).app
        (Y.toEnrichedFunctor.obj (j.obj a)) := by
  change homEquiv Γ a M (restrictionObject j Y)
    (leftKanGradedHomEquiv j Γ (Free.object a M) Y t) = _
  rw [homEquiv_apply, leftKanGradedHomEquiv_app]
  have h := congrArg (fun q => q.app (Y.toEnrichedFunctor.obj (j.obj a)))
    (MonoidalClosed.pre_map (identityInsertion a M) (leftKanUnitComponent j (Free.object a M) a))
  exact (Category.assoc _ _ _).trans (congrArg (fun q => t.app (j.obj a) ≫ q) h.symm)

/-- The inverse uses the original free extension and the original graded coend descent. -/
private theorem lanHomEquiv_symm_apply_private (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V B)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :
    (lanHomEquiv j Γ a M Y).symm f =
      (leftKanGradedHomEquiv j Γ (Free.object a M) Y).symm
        ((homEquiv Γ a M (restrictionObject j Y)).symm f) := rfl

/-- The inverse uses the original free extension and the original graded coend descent. -/
theorem lanHomEquiv_symm_apply (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :
    (lanHomEquiv j Γ a M Y).symm f =
      (leftKanGradedHomEquiv j Γ (Free.object a M) Y).symm
        ((homEquiv Γ a M (restrictionObject j Y)).symm f) :=
  lanHomEquiv_symm_apply_private j Γ a M Y f

/-- Every original coend generator has the exact full raw inverse coefficient image. -/
theorem lanHomEquiv_symm_generator (Γ : Center V) (a : A) (M : V)
    (Y : EnrichedFunctorCat V B)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) (b : B) (a' : A) :
    (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) (Free.object a M).toEnrichedFunctor a') ≫
      GradedNatTrans.gradeFirstComponent Γ ((lanHomEquiv j Γ a M Y).symm f) b =
        lanGenerator j Γ a M Y f b a' := by
  rw [lanHomEquiv_symm_apply]
  have h := leftKanGradedHomEquiv_symm_gradeFirstComponent_ι j Γ (Free.object a M) Y
    ((homEquiv Γ a M (restrictionObject j Y)).symm f) b a'
  have hg := homEquiv_symm_gradeFirst Γ a M (restrictionObject j Y) f a'
  rw [restriction_uncurry] at hg
  exact h.trans (congrArg (fun p =>
    (α_ Γ.1 (j.obj a' ⟶[V] b) (M ⊗ (a ⟶[V] a'))).inv ≫
      ((β_ (j.obj a' ⟶[V] b) Γ.1).inv ▷ (M ⊗ (a ⟶[V] a'))) ≫
      (α_ (j.obj a' ⟶[V] b) Γ.1 (M ⊗ (a ⟶[V] a'))).hom ≫
      ((j.obj a' ⟶[V] b) ◁ p) ≫
      (β_ (j.obj a' ⟶[V] b) (Y.toEnrichedFunctor.obj (j.obj a'))).hom ≫
      MonoidalClosed.uncurry (Y.toEnrichedFunctor.map (j.obj a') b)) hg)

/-- Both complete original free/Lan raw Hom functions are inverse. -/
theorem lanHomEquiv_left_inverse (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor) :
    (lanHomEquiv j Γ a M Y).symm (lanHomEquiv j Γ a M Y t) = t :=
  (lanHomEquiv j Γ a M Y).symm_apply_apply t

/-- The supplied actual free/Lan coefficient arrow is recovered exactly. -/
theorem lanHomEquiv_right_inverse (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :
    lanHomEquiv j Γ a M Y ((lanHomEquiv j Γ a M Y).symm f) = f :=
  (lanHomEquiv j Γ a M Y).apply_symm_apply f

/-- The full all-grade free/Lan correspondence commutes with every central scalar arrow. -/
theorem lanHomEquiv_regrade {Γ Δ : Center V} (h : Γ ⟶ Δ) (a : A) (M : V)
    (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Δ (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor) :
    lanHomEquiv j Γ a M Y (GradedNatTrans.regrade h t) = h.f ≫ lanHomEquiv j Δ a M Y t := by
  change homEquiv Γ a M (restrictionObject j Y)
    (leftKanGradedHomEquiv j Γ (Free.object a M) Y (GradedNatTrans.regrade h t)) = _
  rw [leftKanGradedHomEquiv_regrade, homEquiv_regrade]
  rfl

/-- Original free coefficient maps and actual Lan maps give the same closed pre-map. -/
theorem lanHomEquiv_coefficient (Γ : Center V) (a : A) {M N : V} (f : M ⟶ N)
    (Y : EnrichedFunctorCat V B)
    (t : GradedNatTrans Γ (leftKanObject j (Free.object a N)).toEnrichedFunctor
      Y.toEnrichedFunctor) :
    lanHomEquiv j Γ a M Y (gradedPrecomp Γ ((leftKan j).map (Free.coefficientMap a f)) t) =
      lanHomEquiv j Γ a N Y t ≫ (MonoidalClosed.pre f).app (Y.toEnrichedFunctor.obj (j.obj a)) := by
  change homEquiv Γ a M (restrictionObject j Y)
    (leftKanGradedHomEquiv j Γ (Free.object a M) Y
      (gradedPrecomp Γ ((leftKan j).map (Free.coefficientMap a f)) t)) = _
  rw [leftKanGradedHomEquiv_naturality_left, homEquiv_coefficient]
  rfl

/-- Original target components retain the full target naturality of the actual free/Lan Hom. -/
theorem lanHomEquiv_postcomp (Γ : Center V) (a : A) (M : V)
    {Y Y' : EnrichedFunctorCat V B}
    (t : GradedNatTrans Γ (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor) (q : Y ⟶ Y') :
    lanHomEquiv j Γ a M Y' (gradedPostcomp Γ t q) =
      lanHomEquiv j Γ a M Y t ≫ (ihom M).map (component q (j.obj a)) := by
  change homEquiv Γ a M (restrictionObject j Y')
    (leftKanGradedHomEquiv j Γ (Free.object a M) Y' (gradedPostcomp Γ t q)) = _
  rw [leftKanGradedHomEquiv_naturality_right, homEquiv_postcomp, restrictionMap_component]
  rfl

/-- Inverse free/Lan central naturality retains the actual original scalar map. -/
theorem lanHomEquiv_symm_regrade {Γ Δ : Center V} (h : Γ ⟶ Δ) (a : A) (M : V)
    (Y : EnrichedFunctorCat V B)
    (g : Δ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :
    (lanHomEquiv j Γ a M Y).symm (h.f ≫ g) =
      GradedNatTrans.regrade h ((lanHomEquiv j Δ a M Y).symm g) := by
  apply (lanHomEquiv j Γ a M Y).injective
  rw [Equiv.apply_symm_apply, lanHomEquiv_regrade, Equiv.apply_symm_apply]

/-- Inverse free/Lan coefficient naturality uses the full original free and Lan maps. -/
theorem lanHomEquiv_symm_coefficient (Γ : Center V) (a : A) {M N : V} (f : M ⟶ N)
    (Y : EnrichedFunctorCat V B)
    (g : Γ.1 ⟶ (ihom N).obj (Y.toEnrichedFunctor.obj (j.obj a))) :
    (lanHomEquiv j Γ a M Y).symm
        (g ≫ (MonoidalClosed.pre f).app (Y.toEnrichedFunctor.obj (j.obj a))) =
      gradedPrecomp Γ ((leftKan j).map (Free.coefficientMap a f))
        ((lanHomEquiv j Γ a N Y).symm g) := by
  apply (lanHomEquiv j Γ a M Y).injective
  rw [Equiv.apply_symm_apply, lanHomEquiv_coefficient, Equiv.apply_symm_apply]

/-- Inverse free/Lan target naturality retains the genuine original target transformation. -/
theorem lanHomEquiv_symm_postcomp (Γ : Center V) (a : A) (M : V)
    {Y Y' : EnrichedFunctorCat V B} (q : Y ⟶ Y')
    (g : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) :
    (lanHomEquiv j Γ a M Y').symm (g ≫ (ihom M).map (component q (j.obj a))) =
      gradedPostcomp Γ ((lanHomEquiv j Γ a M Y).symm g) q := by
  apply (lanHomEquiv j Γ a M Y').injective
  rw [Equiv.apply_symm_apply, lanHomEquiv_postcomp, Equiv.apply_symm_apply]

/-- Identity-coefficient evaluation determines the entire actual graded free/Lan transformation. -/
theorem lanHomEquiv_unique (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))
    (t : GradedNatTrans Γ (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor) (h : lanHomEquiv j Γ a M Y t = f) :
    t = (lanHomEquiv j Γ a M Y).symm f := by
  apply (lanHomEquiv j Γ a M Y).injective
  rw [Equiv.apply_symm_apply]
  exact h

/-- Equality on the full original coend generators determines the actual inverse transformation. -/
theorem lanGenerator_unique (Γ : Center V) (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    (f : Γ.1 ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))
    (t : GradedNatTrans Γ (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor)
    (h : ∀ (b : B) (a' : A),
      (Γ.1 ◁ Enriched.weightedCoend.ι (leftKanWeight j b) (Free.object a M).toEnrichedFunctor a') ≫
        GradedNatTrans.gradeFirstComponent Γ t b = lanGenerator j Γ a M Y f b a') :
    t = (lanHomEquiv j Γ a M Y).symm f := by
  apply leftKanGradedGenerator_ext j Γ (Free.object a M) Y
  intro b a'
  exact (h b a').trans (lanHomEquiv_symm_generator j Γ a M Y f b a').symm

/-- The actual free/Lan presheaf correspondence retains the original scalar action. -/
theorem lanHomEquiv_presheaf_naturality (a : A) (M : V) (Y : EnrichedFunctorCat V B)
    {K L : Vᵒᵖ} (h : K ⟶ L)
    (t : (enrichedNatTransYoneda (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor).obj K) :
    lanHomEquiv j ((Center.ofBraided V).obj L.unop) a M Y
        ((enrichedNatTransYoneda (leftKanObject j (Free.object a M)).toEnrichedFunctor
          Y.toEnrichedFunctor).map h t) =
      (yoneda.obj ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))).map h
        (lanHomEquiv j ((Center.ofBraided V).obj K.unop) a M Y t) := by
  have h₁ := lanHomEquiv_apply j ((Center.ofBraided V).obj L.unop) a M Y
    ((enrichedNatTransYoneda (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor).map h t)
  have h₂ := lanHomEquiv_apply j ((Center.ofBraided V).obj K.unop) a M Y t
  have ht : ((enrichedNatTransYoneda (leftKanObject j (Free.object a M)).toEnrichedFunctor
      Y.toEnrichedFunctor).map h t).app (j.obj a) = h.unop ≫ t.app (j.obj a) := rfl
  have hm : (yoneda.obj ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))).map h
      (lanHomEquiv j ((Center.ofBraided V).obj K.unop) a M Y t) =
        h.unop ≫ lanHomEquiv j ((Center.ofBraided V).obj K.unop) a M Y t := rfl
  exact h₁.trans
    ((congrArg (fun p => p ≫ (MonoidalClosed.pre (identityInsertion a M ≫
      leftKanUnitComponent j (Free.object a M) a)).app
        (Y.toEnrichedFunctor.obj (j.obj a))) ht).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun p => h.unop ≫ p) h₂.symm).trans hm.symm)))

/-- The original free/Lan coends represent the actual coefficient transformation presheaf. -/
@[no_expose]
def lanEnrichedNatTransYonedaIso (a : A) (M : V) (Y : EnrichedFunctorCat V B) :
    enrichedNatTransYoneda (leftKanObject j (Free.object a M)).toEnrichedFunctor
        Y.toEnrichedFunctor ⋙ uliftFunctor.{max uA uB vV, max uB vV} ≅
      yoneda.obj ((ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a))) ⋙
        uliftFunctor.{max uA uB vV, vV} :=
  NatIso.ofComponents
    (fun K => (Equiv.ulift.trans
      ((lanHomEquiv j ((Center.ofBraided V).obj K.unop) a M Y).trans Equiv.ulift.symm)).toIso)
    (by
      intro K L h
      apply ConcreteCategory.ext_apply
      intro t
      apply ULift.ext
      exact lanHomEquiv_presheaf_naturality j a M Y h t.down)

private theorem lanEnrichedNatTransYonedaIso_hom_app_private (a : A) (M : V)
    (Y : EnrichedFunctorCat V B) (K : Vᵒᵖ)
    (t : ULift.{max uA uB vV}
      ((enrichedNatTransYoneda (leftKanObject j (Free.object a M)).toEnrichedFunctor
        Y.toEnrichedFunctor).obj K)) :
    (lanEnrichedNatTransYonedaIso j a M Y).hom.app K t =
      ULift.up (lanHomEquiv j ((Center.ofBraided V).obj K.unop) a M Y t.down) := rfl

/-- Every coefficient of the lifted free/Lan presheaf comparison has its original identity image. -/
theorem lanEnrichedNatTransYonedaIso_hom_app (a : A) (M : V)
    (Y : EnrichedFunctorCat V B) (K : Vᵒᵖ)
    (t : ULift.{max uA uB vV}
      ((enrichedNatTransYoneda (leftKanObject j (Free.object a M)).toEnrichedFunctor
        Y.toEnrichedFunctor).obj K)) :
    (lanEnrichedNatTransYonedaIso j a M Y).hom.app K t =
      ULift.up (lanHomEquiv j ((Center.ofBraided V).obj K.unop) a M Y t.down) :=
  lanEnrichedNatTransYonedaIso_hom_app_private j a M Y K t

private theorem lanEnrichedNatTransYonedaIso_inv_app_private (a : A) (M : V)
    (Y : EnrichedFunctorCat V B) (K : Vᵒᵖ)
    (t : ULift.{max uA uB vV} (K.unop ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))) :
    (lanEnrichedNatTransYonedaIso j a M Y).inv.app K t =
      ULift.up ((lanHomEquiv j ((Center.ofBraided V).obj K.unop) a M Y).symm t.down) := rfl

/-- Every inverse presheaf coefficient uses the original full free/coend generator extension. -/
theorem lanEnrichedNatTransYonedaIso_inv_app (a : A) (M : V)
    (Y : EnrichedFunctorCat V B) (K : Vᵒᵖ)
    (t : ULift.{max uA uB vV} (K.unop ⟶ (ihom M).obj (Y.toEnrichedFunctor.obj (j.obj a)))) :
    (lanEnrichedNatTransYonedaIso j a M Y).inv.app K t =
      ULift.up ((lanHomEquiv j ((Center.ofBraided V).obj K.unop) a M Y).symm t.down) :=
  lanEnrichedNatTransYonedaIso_inv_app_private j a M Y K t

end Lan
end CategoryTheory.EnrichedFunctorCat.FreeGraded
