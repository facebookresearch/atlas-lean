/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowGradeStabilization
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowIntrinsicHomology

/-!
# Actual regularization of every correctly graded Ring fraction

An arbitrary projective denominator has an actual complement to a literal
finite free object. The established grade-translation functor transports
the entire numerator grade by that complement. The original epsilon action
and denominator equation preserve the SAME balanced fraction, now over a
regular free-object denominator.

The numerator grade remains the entire free-object K0 grade. Its passage
through finite free components is the separate stabilization argument.
-/

noncomputable section

open CategoryTheory Limits Algebra

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private theorem rowObjectAction_eq (A : AddCommGrpCat.{u}) (q : ℕ)
    (T : FGProjectiveCat.IdempotentModel R)
    (z : SInverseS.coreTranslationHomologyModule (FGProjectiveCat.IdempotentModel R) A q) :
    (SInverseS.coreTranslationHomologyModuleAddCommGrpIso
        (FGProjectiveCat.IdempotentModel R) A q).hom
          (SInverseS.coreTranslationDenominator (FGProjectiveCat.IdempotentModel R)
            (toSkeleton T) • z) =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (nerveMap (SInverseS.coreLeftTranslationFunctor T)) A q
        ((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
          (FGProjectiveCat.IdempotentModel R) A q).hom z) := by
  let C := FGProjectiveCat.IdempotentModel R
  let ε := SInverseS.coreTranslationHomologyModuleAddCommGrpIso C A q
  have h := ConcreteCategory.congr_hom
    (SInverseS.coreTranslationCoefficientMap_comp_moduleIso_hom C A q (toSkeleton T)) z
  change ε.hom
      (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C)) (Multiplicative.ofAdd (toSkeleton T)) • z) =
    SInverseS.coreTranslationHomologyMap C A q (toSkeleton T) (ε.hom z) at h
  exact h.trans (ConcreteCategory.congr_hom
    (SInverseS.coreTranslationHomologyMap_toSkeleton C A q T) (ε.hom z))

/-- Every regular POWER acts on the original core numerator by translation
with the SAME literal finite free object, through the established epsilon Iso. -/
public theorem finiteFreeRowCoreRegularPowerAction_eq
    (A : AddCommGrpCat.{u}) (q k : ℕ)
    (z : SInverseS.coreTranslationHomologyModule (FGProjectiveCat.IdempotentModel R) A q) :
    (SInverseS.coreTranslationHomologyModuleAddCommGrpIso
        (FGProjectiveCat.IdempotentModel R) A q).hom
          (((finiteFreeRowRegularDenominator R) ^ k) • z) =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (SInverseS.coreLeftTranslationFunctor
        ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj k))) A q
        ((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
          (FGProjectiveCat.IdempotentModel R) A q).hom z) := by
  rw [finiteFreeRowRegularDenominator_pow_eq_free]
  exact rowObjectAction_eq R A q _ z

/-- Every actual projective denominator has a derived complement and a
WHOLE grade-translation functor to a literal free grade. Both the actual
complement Iso and the original denominator product are retained. -/
public theorem finiteFreeRowRegularizingGradeFunctor_exists
    (t : Skeleton (FGProjectiveCat.IdempotentModel R)) :
    ∃ (n : ℕ) (Q : FGProjectiveCat.IdempotentModel R)
      (G : SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
        (GrothendieckAddGroup.of t) ⥤
        SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
          (GrothendieckAddGroup.of
            (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))),
      Nonempty (t.out ⊞ Q ≅
        (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n) ∧
      G ⋙ (SInverseS.coreGradeProperty (C := FGProjectiveCat.IdempotentModel R)
          (GrothendieckAddGroup.of
            (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))).ι =
        (SInverseS.coreGradeProperty (C := FGProjectiveCat.IdempotentModel R)
          (GrothendieckAddGroup.of t)).ι ⋙ SInverseS.coreLeftTranslationFunctor Q ∧
      SInverseS.coreTranslationDenominator (FGProjectiveCat.IdempotentModel R) t *
          SInverseS.coreTranslationDenominator (FGProjectiveCat.IdempotentModel R) (toSkeleton Q) =
        (finiteFreeRowRegularDenominator R) ^ n := by
  let C := FGProjectiveCat.IdempotentModel R
  obtain ⟨n, Q, ⟨e⟩⟩ := RingK0.idempotent_exists_biprod_iso_free R t.out
  let P := (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n
  have hSkeleton : t + toSkeleton Q = toSkeleton P := by
    have h := (Skeleton.toSkeleton_biprod t.out Q).symm.trans (congr_toSkeleton_of_iso e)
    have hOut : toSkeleton t.out = t := Quotient.out_eq t
    change toSkeleton t.out + toSkeleton Q = toSkeleton P at h
    exact (congrArg (fun a : Skeleton C => a + toSkeleton Q) hOut.symm).trans h
  let g := GrothendieckAddGroup.of t
  let a := GrothendieckAddGroup.of (toSkeleton Q) + g
  let b := GrothendieckAddGroup.of (toSkeleton P)
  have hClass : a = b := by
    have h := congrArg GrothendieckAddGroup.of hSkeleton
    simp only [map_add] at h
    exact (add_comm _ _).trans h
  let hLE : SInverseS.coreGradeProperty (C := C) a ≤
      SInverseS.coreGradeProperty (C := C) b := fun X h => h.trans hClass
  let L := SInverseS.coreGradeLeftTranslationFunctor (C := C) Q g
  let G := L ⋙ ObjectProperty.ιOfLE hLE
  have hForget : ObjectProperty.ιOfLE hLE ⋙ (SInverseS.coreGradeProperty (C := C) b).ι =
      (SInverseS.coreGradeProperty (C := C) a).ι := rfl
  have hG : G ⋙ (SInverseS.coreGradeProperty (C := C) b).ι =
      (SInverseS.coreGradeProperty (C := C) g).ι ⋙ SInverseS.coreLeftTranslationFunctor Q :=
    (Functor.assoc L (ObjectProperty.ιOfLE hLE) _).trans
      ((congrArg (fun F => L ⋙ F) hForget).trans
        (SInverseS.coreGradeLeftTranslationFunctor_comp_ι (C := C) Q g))
  have hDenominator : SInverseS.coreTranslationDenominator C t *
      SInverseS.coreTranslationDenominator C (toSkeleton Q) =
        (finiteFreeRowRegularDenominator R) ^ n := by
    rw [finiteFreeRowRegularDenominator_pow_eq_free]
    apply Subtype.ext
    let φ : Multiplicative (Skeleton C) →* SInverseS.coreTranslationRing C :=
      MonoidAlgebra.of ℤ (Multiplicative (Skeleton C))
    change φ (Multiplicative.ofAdd t) * φ (Multiplicative.ofAdd (toSkeleton Q)) =
      φ (Multiplicative.ofAdd (toSkeleton P))
    have hMul : Multiplicative.ofAdd t * Multiplicative.ofAdd (toSkeleton Q) =
        Multiplicative.ofAdd (toSkeleton P) := congrArg Multiplicative.ofAdd hSkeleton
    exact (φ.map_mul _ _).symm.trans (congrArg φ hMul)
  exact ⟨n, Q, G, ⟨e⟩, hG, hDenominator⟩

/-- Every correctly graded original fraction has a regular-denominator
representative with numerator in the ENTIRE corresponding free-object K0
grade. The numerator and denominator are translated together by an actual
derived projective complement; no image or homology-Iso input is used. -/
public theorem finiteFreeRowZeroFraction_exists_regular_grade
    (A : AddCommGrpCat.{u}) (q : ℕ)
    (t : Skeleton (FGProjectiveCat.IdempotentModel R))
    (y : (nerve (SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
      (GrothendieckAddGroup.of t))).homology (C := AddCommGrpCat.{u}) A q) :
    ∃ (n : ℕ)
      (z : (nerve (SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
        (GrothendieckAddGroup.of
          (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))))).homology
            (C := AddCommGrpCat.{u}) A q),
      (SInverseS.zeroCoreFraction (C := FGProjectiveCat.IdempotentModel R) A q t y :
        CategoryTheory.SInverseS.localizedCoreTranslationHomology
          (FGProjectiveCat.IdempotentModel R) A q) =
        LocalizedModule.mk
          (R := CategoryTheory.SInverseS.coreTranslationRing
            (FGProjectiveCat.IdempotentModel R))
          (S := CategoryTheory.SInverseS.coreTranslationDenominators
            (FGProjectiveCat.IdempotentModel R))
          (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
            (FGProjectiveCat.IdempotentModel R) A q)
          (((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
            (FGProjectiveCat.IdempotentModel R) A q).inv
            (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap (SInverseS.coreGradeProperty
              (C := FGProjectiveCat.IdempotentModel R)
              (GrothendieckAddGroup.of
                (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))).ι) A q z)) :
            CategoryTheory.SInverseS.coreTranslationHomologyModuleCat
              (FGProjectiveCat.IdempotentModel R) A q)
          ((finiteFreeRowRegularDenominator R) ^ n) := by
  let C := FGProjectiveCat.IdempotentModel R
  obtain ⟨n, Q, G, _, hG, hDenominator⟩ := finiteFreeRowRegularizingGradeFunctor_exists R t
  let g := GrothendieckAddGroup.of t
  let b := GrothendieckAddGroup.of
    (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))
  let i := (SInverseS.coreGradeProperty (C := C) g).ι
  let j := (SInverseS.coreGradeProperty (C := C) b).ι
  let T := SInverseS.coreLeftTranslationFunctor Q
  let ε := SInverseS.coreTranslationHomologyModuleAddCommGrpIso C A q
  let d := SInverseS.coreTranslationDenominator C t
  let e := SInverseS.coreTranslationDenominator C (toSkeleton Q)
  let z := SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap G) A q y
  let a : CategoryTheory.SInverseS.coreTranslationHomologyModuleCat C A q :=
    ε.inv (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap i) A q y)
  let a' : CategoryTheory.SInverseS.coreTranslationHomologyModuleCat C A q :=
    ε.inv (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap j) A q z)
  have hSquare : SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap G) A q ≫
      SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap j) A q =
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap i) A q ≫ SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap T) A q := by
    have h := congrArg (fun F => SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap F) A q) hG
    simpa only [← nerveMap_comp, SSet.homologyMap_comp] using h
  have hValue : SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap j) A q z =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (nerveMap T) A q (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap i) A q y) :=
    ConcreteCategory.congr_hom hSquare y
  have hAction : ε.hom (e • a) =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (nerveMap T) A q (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap i) A q y) :=
    (rowObjectAction_eq R A q Q a).trans
      (congrArg (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap T) A q)
        (Iso.inv_hom_id_apply ε (SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap i) A q y)))
  have hNumerator : a' = e • a :=
    (congrArg ε.inv hValue).trans
      ((congrArg ε.inv hAction.symm).trans (Iso.hom_inv_id_apply ε (e • a)))
  refine ⟨n, z, ?_⟩
  calc
    (SInverseS.zeroCoreFraction (C := C) A q t y :
      CategoryTheory.SInverseS.localizedCoreTranslationHomology
        (FGProjectiveCat.IdempotentModel R) A q) = LocalizedModule.mk
          (R := CategoryTheory.SInverseS.coreTranslationRing
            (FGProjectiveCat.IdempotentModel R))
          (S := CategoryTheory.SInverseS.coreTranslationDenominators
            (FGProjectiveCat.IdempotentModel R))
          (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
            (FGProjectiveCat.IdempotentModel R) A q)
          a d :=
      SInverseS.zeroCoreFraction_eq_mk (C := C) A q t y
    _ = LocalizedModule.mk
      (R := CategoryTheory.SInverseS.coreTranslationRing
        (FGProjectiveCat.IdempotentModel R))
      (S := CategoryTheory.SInverseS.coreTranslationDenominators
        (FGProjectiveCat.IdempotentModel R))
      (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
        (FGProjectiveCat.IdempotentModel R) A q)
      (e • a) (d * e) :=
      (LocalizedModule.mk_cancel_common_right d e a).symm
    _ = LocalizedModule.mk
      (R := CategoryTheory.SInverseS.coreTranslationRing
        (FGProjectiveCat.IdempotentModel R))
      (S := CategoryTheory.SInverseS.coreTranslationDenominators
        (FGProjectiveCat.IdempotentModel R))
      (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
        (FGProjectiveCat.IdempotentModel R) A q)
      a' (d * e) :=
      congrArg (fun x => LocalizedModule.mk
        (R := CategoryTheory.SInverseS.coreTranslationRing
          (FGProjectiveCat.IdempotentModel R))
        (S := CategoryTheory.SInverseS.coreTranslationDenominators
          (FGProjectiveCat.IdempotentModel R))
        (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
          (FGProjectiveCat.IdempotentModel R) A q)
        x (d * e)) hNumerator.symm
    _ = LocalizedModule.mk
      (R := CategoryTheory.SInverseS.coreTranslationRing
        (FGProjectiveCat.IdempotentModel R))
      (S := CategoryTheory.SInverseS.coreTranslationDenominators
        (FGProjectiveCat.IdempotentModel R))
      (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
        (FGProjectiveCat.IdempotentModel R) A q)
      a' ((finiteFreeRowRegularDenominator R) ^ n) :=
      congrArg (fun s => LocalizedModule.mk
        (R := CategoryTheory.SInverseS.coreTranslationRing
          (FGProjectiveCat.IdempotentModel R))
        (S := CategoryTheory.SInverseS.coreTranslationDenominators
          (FGProjectiveCat.IdempotentModel R))
        (M := CategoryTheory.SInverseS.coreTranslationHomologyModule
          (FGProjectiveCat.IdempotentModel R) A q)
        a' s) hDenominator

end AlgebraicKTheory.StableGL
