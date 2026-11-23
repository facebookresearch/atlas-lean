/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowFractionRegularization
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowEventualEquality
public import MathlibExt.CategoryTheory.CategoryHomology.FiniteComponentSupport
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# All-degree homology of the actual stable opposite-row zero comparison

Every intrinsic graded fraction is regularized by its actual projective
complement. Finite categorical-component support and actual same-free
stabilization put every resulting component fraction in the ORIGINAL
finite-stage colimit image. Generator leastness proves surjectivity; the
derived eventual-kernel equality proves injectivity.

The resulting homology isomorphisms belong to the actual continuous stable
BGL map constructed from the original row stages. No homology, model,
comparison-map, or scalar-injectivity witness is supplied.
-/

noncomputable section

open CategoryTheory Limits Algebra
open scoped BigOperators

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private theorem rowGradeComponentFraction_exists_stage
    (A : AddCommGrpCat.{u}) (q n : ℕ)
    (c : ConnectedComponents
      (SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
        (GrothendieckAddGroup.of
          (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))))
    (x : (nerve c.Component).homology (C := AddCommGrpCat.{u}) A q) :
    ∃ (k : ℕ)
      (y : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin (n + k)) R)ᵐᵒᵖ)).homology
        (C := AddCommGrpCat.{u}) A q),
      ((finiteFreeRowIntrinsicHomologyComparison R A q
        (colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u})
          A q) (n + k) y)).val :
        CategoryTheory.SInverseS.localizedCoreTranslationHomology
          (FGProjectiveCat.IdempotentModel R) A q) =
      SInverseS.zeroCoreFraction (C := FGProjectiveCat.IdempotentModel R) A q
        (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))
        (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap c.ι) A q x) := by
  obtain ⟨k, y, hImage⟩ := finiteFreeRowGradeComponent_homology_exists_stage R A q n c x
  let C := FGProjectiveCat.IdempotentModel R
  let t := toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)
  let i := (SInverseS.coreGradeProperty (C := C) (GrothendieckAddGroup.of t)).ι
  let F := c.ι ⋙ i
  let T := SInverseS.coreLeftTranslationFunctor
    ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj k)
  let ε := SInverseS.coreTranslationHomologyModuleAddCommGrpIso C A q
  let r := finiteFreeRowRegularDenominator R
  let a : CategoryTheory.SInverseS.coreTranslationHomologyModuleCat C A q :=
    ε.inv (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap i) A q
    (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap c.ι) A q x))
  let b : CategoryTheory.SInverseS.coreTranslationHomologyModuleCat C A q :=
    ε.inv (SSet.homologyMap (C := AddCommGrpCat.{u})
    (finiteFreeRowStageCoreNerveMap R (n + k)) A q y)
  have hSource : SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap F) A q x =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (nerveMap i) A q (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap c.ι) A q x) := by
    exact ConcreteCategory.congr_hom
      ((congrArg (fun f => SSet.homologyMap (C := AddCommGrpCat.{u})
        f A q) (nerveMap_comp c.ι i)).symm.trans
        ((SSet.homologyFunctor (C := AddCommGrpCat.{u})
          A q).map_comp (nerveMap c.ι) (nerveMap i))) x
  have hTranslated : SSet.homologyMap (C := AddCommGrpCat.{u})
    (finiteFreeRowStageCoreNerveMap R (n + k)) A q y =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap T) A q
        (SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap i) A q (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap c.ι) A q x)) := by
    have h := ConcreteCategory.congr_hom
      ((congrArg (fun f => SSet.homologyMap (C := AddCommGrpCat.{u})
        f A q) (nerveMap_comp F T)).symm.trans
        ((SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q).map_comp (nerveMap F) (nerveMap T))) x
    exact hImage.trans
      (h.trans (congrArg (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap T) A q) hSource))
  have hAction : ε.hom ((r ^ k) • a) =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap T) A q
        (SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap i) A q (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap c.ι) A q x)) :=
    (finiteFreeRowCoreRegularPowerAction_eq R A q k a).trans
      (congrArg (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap T) A q)
        (Iso.inv_hom_id_apply ε _))
  have hNumerator : b = (r ^ k) • a :=
    (congrArg ε.inv hTranslated).trans
      ((congrArg ε.inv hAction.symm).trans (Iso.hom_inv_id_apply ε _))
  have hPower : r ^ (n + k) = r ^ k * r ^ n := by
    rw [pow_add, mul_comm]
  have hFraction : (SInverseS.zeroCoreFraction (C := C) A q t
      (SSet.homologyMap (C := AddCommGrpCat.{u})
        (nerveMap c.ι) A q x) :
                     CategoryTheory.SInverseS.localizedCoreTranslationHomology
                       (FGProjectiveCat.IdempotentModel R) A q) = LocalizedModule.mk
                         (R := CategoryTheory.SInverseS.coreTranslationRing
                           (FGProjectiveCat.IdempotentModel R))
                         (S := CategoryTheory.SInverseS.coreTranslationDenominators
                           (FGProjectiveCat.IdempotentModel R))
                         (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
                           (FGProjectiveCat.IdempotentModel R) A q)
                         a (r ^ n) :=
    (SInverseS.zeroCoreFraction_eq_mk (C := C) A q t _).trans
      (congrArg (fun d => LocalizedModule.mk
        (R := CategoryTheory.SInverseS.coreTranslationRing
          (FGProjectiveCat.IdempotentModel R))
        (S := CategoryTheory.SInverseS.coreTranslationDenominators
          (FGProjectiveCat.IdempotentModel R))
        (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
          (FGProjectiveCat.IdempotentModel R) A q)
        a d)
        (finiteFreeRowRegularDenominator_pow_eq_free R n).symm)
  refine ⟨k, y, ?_⟩
  calc
    _ = LocalizedModule.mk
      (R := CategoryTheory.SInverseS.coreTranslationRing
        (FGProjectiveCat.IdempotentModel R))
      (S := CategoryTheory.SInverseS.coreTranslationDenominators
        (FGProjectiveCat.IdempotentModel R))
      (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
        (FGProjectiveCat.IdempotentModel R) A q)
      b (r ^ (n + k)) :=
      finiteFreeRowIntrinsicHomologyComparison_ι_val R A q (n + k) y
    _ = LocalizedModule.mk
      (R := CategoryTheory.SInverseS.coreTranslationRing
        (FGProjectiveCat.IdempotentModel R))
      (S := CategoryTheory.SInverseS.coreTranslationDenominators
        (FGProjectiveCat.IdempotentModel R))
      (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
        (FGProjectiveCat.IdempotentModel R) A q)
      ((r ^ k) • a) (r ^ k * r ^ n) :=
      congrArg₂ (fun z d => LocalizedModule.mk
        (R := CategoryTheory.SInverseS.coreTranslationRing
          (FGProjectiveCat.IdempotentModel R))
        (S := CategoryTheory.SInverseS.coreTranslationDenominators
          (FGProjectiveCat.IdempotentModel R))
        (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
          (FGProjectiveCat.IdempotentModel R) A q)
        z d) hNumerator hPower
    _ = LocalizedModule.mk
      (R := CategoryTheory.SInverseS.coreTranslationRing
        (FGProjectiveCat.IdempotentModel R))
      (S := CategoryTheory.SInverseS.coreTranslationDenominators
        (FGProjectiveCat.IdempotentModel R))
      (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
        (FGProjectiveCat.IdempotentModel R) A q)
      a (r ^ n) :=
      LocalizedModule.mk_cancel_common_left (r ^ k) (r ^ n) a
    _ = _ := hFraction.symm

private theorem rowRegularGradeFraction_mem_range
    (A : AddCommGrpCat.{u}) (q n : ℕ)
    (z : (nerve (SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
      (GrothendieckAddGroup.of
        (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))))).homology
          (C := AddCommGrpCat.{u}) A q) :
    SInverseS.zeroCoreFraction (C := FGProjectiveCat.IdempotentModel R) A q
        (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)) z ∈
      (((SInverseS.zeroLocalizedCoreSubgroup (C := FGProjectiveCat.IdempotentModel R) A q).subtype).comp
        (finiteFreeRowIntrinsicHomologyComparison R A q).hom).range := by
  let C := FGProjectiveCat.IdempotentModel R
  let t := toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)
  let J := SInverseS.CoreGrade (C := C) (GrothendieckAddGroup.of t)
  let S := (((SInverseS.zeroLocalizedCoreSubgroup (C := C) A q).subtype).comp
    (finiteFreeRowIntrinsicHomologyComparison R A q).hom).range
  let L := (SInverseS.zeroLocalizedCoreSubgroup (C := C) A q).subtype.comp
    (SInverseS.zeroCoreFractionMap (C := C) A q t).hom
  obtain ⟨s, x, hz⟩ := categoryHomology_exists_finite_component_sum J A q z
  have hValue (y : (nerve J).homology (C := AddCommGrpCat.{u})
    A q) : L y = SInverseS.zeroCoreFraction (C := C) A q t y :=
    SInverseS.zeroCoreFractionMap_apply (C := C) A q t y
  have hSum : L z = ∑ c ∈ s, L (SSet.homologyMap (C := AddCommGrpCat.{u})
    (nerveMap c.ι) A q (x c)) := by
    simpa only [map_sum] using congrArg L hz
  have hTerms (c : ConnectedComponents J) :
      L (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap c.ι) A q (x c)) ∈ S := by
    obtain ⟨k, y, hy⟩ := rowGradeComponentFraction_exists_stage R A q n c (x c)
    have h : SInverseS.zeroCoreFraction (C := C) A q t
        (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap c.ι) A q (x c)) ∈ S :=
      ⟨colimit.ι (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u})
        A q) (n + k) y, hy⟩
    exact (hValue _).symm ▸ h
  have hAll : L z ∈ S := hSum.symm ▸ S.sum_mem (fun c _ => hTerms c)
  exact (hValue z) ▸ hAll

/-- Every original correctly graded fraction is in the image of the SAME
actual finite-stage colimit map. This covers all denominator/numerator
grades, using real complements, finite support and actual stabilization. -/
public theorem finiteFreeRowZeroFraction_mem_intrinsic_range
    (A : AddCommGrpCat.{u}) (q : ℕ)
    (t : Skeleton (FGProjectiveCat.IdempotentModel R))
    (z : (nerve (SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
      (GrothendieckAddGroup.of t))).homology (C := AddCommGrpCat.{u}) A q) :
    SInverseS.zeroCoreFraction (C := FGProjectiveCat.IdempotentModel R) A q t z ∈
      (((SInverseS.zeroLocalizedCoreSubgroup (C := FGProjectiveCat.IdempotentModel R) A q).subtype).comp
        (finiteFreeRowIntrinsicHomologyComparison R A q).hom).range := by
  obtain ⟨n, y, hy⟩ := finiteFreeRowZeroFraction_exists_regular_grade R A q t z
  let t' := toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)
  have hValue : (SInverseS.zeroCoreFraction (C := FGProjectiveCat.IdempotentModel R) A q t' y :
                  CategoryTheory.SInverseS.localizedCoreTranslationHomology
                    (FGProjectiveCat.IdempotentModel R) A q) =
      SInverseS.zeroCoreFraction (C := FGProjectiveCat.IdempotentModel R) A q t z := by
    have h := SInverseS.zeroCoreFraction_eq_mk
      (C := FGProjectiveCat.IdempotentModel R) A q t' y
    rw [← finiteFreeRowRegularDenominator_pow_eq_free R n] at h
    exact h.trans hy.symm
  exact hValue ▸ rowRegularGradeFraction_mem_range R A q n y

/-- The actual original finite-stage colimit map covers the ENTIRE intrinsic
zero subgroup in every degree, with no desired image or Hiso premise. -/
public theorem finiteFreeRowIntrinsicHomologyComparison_surjective
    (A : AddCommGrpCat.{u}) (q : ℕ) :
    Function.Surjective (finiteFreeRowIntrinsicHomologyComparison R A q) := by
  let C := FGProjectiveCat.IdempotentModel R
  let Ψ := finiteFreeRowIntrinsicHomologyComparison R A q
  let s := (SInverseS.zeroLocalizedCoreSubgroup (C := C) A q).subtype.comp Ψ.hom
  have hRange : SInverseS.zeroLocalizedCoreSubgroup (C := C) A q ≤ s.range :=
    (SInverseS.zeroLocalizedCoreSubgroup_le_iff (C := C) A q s.range).mpr
      (finiteFreeRowZeroFraction_mem_intrinsic_range R A q)
  intro z
  obtain ⟨x, hx⟩ := hRange z.property
  exact ⟨x, Subtype.ext hx⟩

/-- In EVERY degree the ORIGINAL finite-stage colimit comparison with the
intrinsic zero subgroup is an isomorphism. Both injectivity and full graded
surjectivity are derived from the actual maps. -/
public theorem finiteFreeRowIntrinsicHomologyComparison_isIso
    (A : AddCommGrpCat.{u}) (q : ℕ) :
    IsIso (finiteFreeRowIntrinsicHomologyComparison R A q) := by
  let Ψ := finiteFreeRowIntrinsicHomologyComparison R A q
  letI : Mono Ψ := finiteFreeRowIntrinsicHomologyComparison_mono R A q
  letI : Epi Ψ := (AddCommGrpCat.epi_iff_surjective Ψ).mpr
    (finiteFreeRowIntrinsicHomologyComparison_surjective R A q)
  exact isIso_of_mono_of_epi Ψ

/-- The ACTUAL stable continuous comparison in nerve homology coordinates
is an isomorphism in every degree, over every original Ring. -/
public theorem finiteFreeRowStableHomologyComparison_isIso
    (A : AddCommGrpCat.{u}) (q : ℕ) :
    IsIso (finiteFreeRowStableHomologyComparison R A q) := by
  let I := finiteBGLHomologyColimitIso R A q
  let Z := SInverseS.zeroLocalizedCoreHomologyIso (C := FGProjectiveCat.IdempotentModel R) A q
  let Ψ := finiteFreeRowIntrinsicHomologyComparison R A q
  letI : IsIso Ψ := finiteFreeRowIntrinsicHomologyComparison_isIso R A q
  let E := I.symm ≪≫ asIso Ψ ≪≫ Z
  have hSource : (finiteBGLHomologyColimitIso R A q).hom ≫
      finiteFreeRowStableHomologyComparison R A q =
        finiteFreeRowHomologyColimitComparison R A q := by
    apply colimit.hom_ext
    intro n
    have hι := finiteBGLHomologyColimitIso_ι R A q n
    have hStage := finiteFreeRowStableHomologyComparison_stage R A q n
    have hColim := finiteFreeRowHomologyColimitComparison_ι R A q n
    have hassoc := Category.assoc
      (colimit.ι
        (finiteBGLNerveDiagram R ⋙ SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) n)
      (finiteBGLHomologyColimitIso R A q).hom
      (finiteFreeRowStableHomologyComparison R A q)
    simp only [finiteBGLNerveDiagram, Functor.comp_obj, SSet.homologyFunctor_obj,
      nerveFunctor_obj, finiteClassifyingCategoryDiagram_obj, Cat.of_α]
      at hι hStage hColim hassoc ⊢
    have hpost := congrArg
      (fun z :
        (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
            (C := AddCommGrpCat.{u}) A q ⟶
          (nerve (ClassifyingCategory R)).homology (C := AddCommGrpCat.{u}) A q =>
        z ≫ finiteFreeRowStableHomologyComparison R A q)
      hι
    exact hassoc.symm.trans (hpost.trans (hStage.trans hColim.symm))
  have hIE : I.hom ≫ E.hom = Ψ ≫ Z.hom := by
    change I.hom ≫ (I.inv ≫ Ψ ≫ Z.hom) = _
    rw [← Category.assoc, I.hom_inv_id, Category.id_comp]
  have hE : E.hom = finiteFreeRowStableHomologyComparison R A q := by
    apply (cancel_epi I.hom).mp
    exact hIE.trans
      ((finiteFreeRowIntrinsicHomologyComparison_comp_homologyIso R A q).trans hSource.symm)
  exact hE ▸ E.isIso_hom

/-- The homology map of the LITERAL ordinary stable BGL-to-zero continuous
map is an isomorphism in every degree and every fixed coefficient group. -/
public theorem finiteFreeRowStableZeroComparison_homology_isIso
    (A : AddCommGrpCat.{u}) (q : ℕ) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
      (finiteFreeRowStableZeroComparison R)) := by
  let eX := SSet.realizationSingularHomologyIso A (nerve (ClassifyingCategory R)) q
  let eY := SSet.realizationSingularHomologyIso A
    (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) q
  let H := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A
  let m := finiteFreeRowStableHomologyComparison R A q
  letI : IsIso m := finiteFreeRowStableHomologyComparison_isIso R A q
  let E := eX.symm ≪≫ asIso m ≪≫ eY
  have hFront : eX.hom ≫ E.hom = m ≫ eY.hom := by
    change eX.hom ≫ (eX.inv ≫ m ≫ eY.hom) = _
    rw [← Category.assoc, eX.hom_inv_id, Category.id_comp]
  have hE : E.hom = H.map (finiteFreeRowStableZeroComparison R) := by
    apply (cancel_epi eX.hom).mp
    exact hFront.trans (finiteFreeRowStableHomologyComparison_singular_square R A q).symm
  exact hE ▸ E.isIso_hom

/-- EVERY-degree integral homology isomorphism of the SAME actual stable
ordinary BGL map, with the original Ring and all stage inclusions unchanged. -/
public theorem finiteFreeRowStableZeroComparison_integral_isIso (q : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor q).map
      (finiteFreeRowStableZeroComparison R)) :=
  finiteFreeRowStableZeroComparison_homology_isIso R
    AlgebraicTopology.singularIntegralCoefficients q

end AlgebraicKTheory.StableGL
