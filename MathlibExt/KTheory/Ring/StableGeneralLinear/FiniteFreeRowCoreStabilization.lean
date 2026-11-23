/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowCoreHomology
public import MathlibExt.CategoryTheory.Monoidal.SInverseSFiberHomologyModuleComparison

/-!
# Actual block stabilization and the original regular core action

The original row successor Iso supplies the core translation/block
stabilization square in every homological degree. The established epsilon
comparison identifies the regular monomial action with that SAME left
translation map. Thus the numerator of the next original finite stage is
exactly regular multiplication of the previous numerator.

The localized zero-grade fraction compatibility uses this numerator shift
together with the simultaneous denominator shift.
-/

noncomputable section

open CategoryTheory Limits Algebra

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

private theorem rowCoreStageNerve_eq_up (n : ℕ) :
    finiteFreeRowStageCoreNerveMap R n =
      nerveMapCommonHomUp.{0, u, 0} (finiteFreeRowCoreModelFunctor R n) := by
  ext Δ X
  exact (finiteFreeRowStageCoreNerveMap_app R n Δ X).trans
    (nerveMapCommonHomUp_app (finiteFreeRowCoreModelFunctor R n) Δ X).symm

/-- EVERY-degree core left translation is the literal original block
stabilization on the SAME original finite-row homology classes. -/
public theorem finiteFreeRowStageCoreHomology_stabilization_square
    (A : AddCommGrpCat.{u}) (q n : ℕ) :
    SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q ≫
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap (SInverseS.coreLeftTranslationFunctor
            ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)))) A q =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        ((finiteBGLNerveDiagram R).map (homOfLE (Nat.le_succ n))) A q ≫
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (finiteFreeRowStageCoreNerveMap R (n + 1)) A q := by
  let T := SInverseS.coreLeftTranslationFunctor
    ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ))
  let s := (finiteBGLNerveDiagram R).map (homOfLE (Nat.le_succ n))
  let S := finiteOppositeGLRowStabilizationFunctor R n
  let F := finiteFreeRowCoreModelFunctor R n
  let G := finiteFreeRowCoreModelFunctor R (n + 1)
  let J : F ⋙ T ≅ S ⋙ G := finiteFreeRowCoreSuccessorNatIso R n
  have h₀ : finiteFreeRowStageCoreNerveMap R n ≫ nerveMap T =
      nerveMapCommonHomUp.{0, u, 0} (F ⋙ T) :=
    (congrArg (fun f => f ≫ nerveMap T) (rowCoreStageNerve_eq_up R n)).trans
      (nerveMapCommonHomUp_nerveMap_comp.{0, u, 0} F T)
  have h₁ : s ≫ finiteFreeRowStageCoreNerveMap R (n + 1) =
      nerveMapCommonHomUp.{0, u, 0} (S ⋙ G) :=
    (congrArg (fun f => f ≫ finiteFreeRowStageCoreNerveMap R (n + 1))
      (finiteFreeRowOriginalNerveSuccessor_eq R n)).trans
        ((congrArg (fun g => nerveMap S ≫ g) (rowCoreStageNerve_eq_up R (n + 1))).trans
          (nerveMap_nerveMapCommonHomUp_comp.{0, u, 0} S G))
  have hH :
      SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMapCommonHomUp.{0, u, 0} (F ⋙ T)) A q =
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMapCommonHomUp.{0, u, 0} (S ⋙ G)) A q :=
    SSet.Homotopy.congr_homologyMap (C := AddCommGrpCat.{u})
      (NatTrans.nerveHomotopyCommonHomUp.{0, u, 0} J.hom) A q
  have h : SSet.homologyMap (C := AddCommGrpCat.{u})
    (finiteFreeRowStageCoreNerveMap R n ≫ nerveMap T) A q =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (s ≫ finiteFreeRowStageCoreNerveMap R (n + 1)) A q :=
    (congrArg (fun f => SSet.homologyMap (C := AddCommGrpCat.{u}) f A q) h₀).trans
      (hH.trans (congrArg (fun f => SSet.homologyMap (C := AddCommGrpCat.{u}) f A q) h₁).symm)
  have hComp₀ :
      SSet.homologyMap (C := AddCommGrpCat.{u})
          (finiteFreeRowStageCoreNerveMap R n ≫ nerveMap T) A q =
        SSet.homologyMap (C := AddCommGrpCat.{u})
            (finiteFreeRowStageCoreNerveMap R n) A q ≫
          SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap T) A q := by
    exact SSet.homologyMap_comp (C := AddCommGrpCat.{u})
      (f := finiteFreeRowStageCoreNerveMap R n) (g := nerveMap T) (R := A) (n := q)
  have hComp₁ :
      SSet.homologyMap (C := AddCommGrpCat.{u})
          (s ≫ finiteFreeRowStageCoreNerveMap R (n + 1)) A q =
        SSet.homologyMap (C := AddCommGrpCat.{u}) s A q ≫
          SSet.homologyMap (C := AddCommGrpCat.{u})
            (finiteFreeRowStageCoreNerveMap R (n + 1)) A q := by
    exact SSet.homologyMap_comp (C := AddCommGrpCat.{u})
      (f := s) (g := finiteFreeRowStageCoreNerveMap R (n + 1)) (R := A) (n := q)
  exact hComp₀.symm.trans (h.trans hComp₁)

/-- The original epsilon/core-homology identification takes regular
monomial multiplication to the SAME literal free-one core translation. -/
public theorem finiteFreeRowCoreRegularAction_eq
    (A : AddCommGrpCat.{u}) (q : ℕ)
    (z : SInverseS.coreTranslationHomologyModule (FGProjectiveCat.IdempotentModel R) A q) :
    (SInverseS.coreTranslationHomologyModuleAddCommGrpIso
        (FGProjectiveCat.IdempotentModel R) A q).hom
          ((finiteFreeRowRegularDenominator R) • z) =
      SSet.homologyMap (C := AddCommGrpCat.{u})
        (nerveMap (SInverseS.coreLeftTranslationFunctor
          ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)))) A q
        ((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
          (FGProjectiveCat.IdempotentModel R) A q).hom z) := by
  let C := FGProjectiveCat.IdempotentModel R
  let T := (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)
  let t := toSkeleton T
  let ε := SInverseS.coreTranslationHomologyModuleAddCommGrpIso C A q
  have h := ConcreteCategory.congr_hom
    (SInverseS.coreTranslationCoefficientMap_comp_moduleIso_hom C A q t) z
  change ε.hom
      (MonoidAlgebra.of ℤ (Multiplicative (Skeleton C)) (Multiplicative.ofAdd t) • z) =
    SInverseS.coreTranslationHomologyMap C A q t (ε.hom z) at h
  change ε.hom ((finiteFreeRowRegularDenominator R : SInverseS.coreTranslationRing C) • z) = _
  rw [finiteFreeRowRegularDenominator_val]
  exact h.trans (ConcreteCategory.congr_hom
    (SInverseS.coreTranslationHomologyMap_toSkeleton C A q T) (ε.hom z))

/-- The numerator of the next ORIGINAL finite stage is regular multiplication
of its predecessor numerator, for every original class and every degree. -/
public theorem finiteFreeRowStageCoreNumerator_succ
    (A : AddCommGrpCat.{u}) (q n : ℕ)
    (x : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)).homology
      (C := AddCommGrpCat.{u}) A q) :
    (SInverseS.coreTranslationHomologyModuleAddCommGrpIso
        (FGProjectiveCat.IdempotentModel R) A q).inv
      (SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R (n + 1)) A q
        (SSet.homologyMap (C := AddCommGrpCat.{u})
          ((finiteBGLNerveDiagram R).map (homOfLE (Nat.le_succ n))) A q x)) =
      @SMul.smul
        ↥(SInverseS.coreTranslationDenominators (FGProjectiveCat.IdempotentModel R))
        (SInverseS.coreTranslationHomologyModuleCat
          (FGProjectiveCat.IdempotentModel R) A q)
        inferInstance (finiteFreeRowRegularDenominator R)
        (((SInverseS.coreTranslationHomologyModuleAddCommGrpIso
          (FGProjectiveCat.IdempotentModel R) A q).inv
            (SSet.homologyMap (C := AddCommGrpCat.{u})
              (finiteFreeRowStageCoreNerveMap R n) A q x)) :
          SInverseS.coreTranslationHomologyModuleCat
            (FGProjectiveCat.IdempotentModel R) A q) := by
  let C := FGProjectiveCat.IdempotentModel R
  let ε := SInverseS.coreTranslationHomologyModuleAddCommGrpIso C A q
  let a := SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R n) A q x
  let y : SInverseS.coreTranslationHomologyModuleCat C A q := ε.inv a
  let b := SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R (n + 1)) A q
    (SSet.homologyMap (C := AddCommGrpCat.{u})
      ((finiteBGLNerveDiagram R).map (homOfLE (Nat.le_succ n))) A q x)
  let T := SSet.homologyMap (C := AddCommGrpCat.{u})
    (nerveMap (SInverseS.coreLeftTranslationFunctor
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (1 : ℕ)))) A q
  have hSquare : T a = b := ConcreteCategory.congr_hom
    (finiteFreeRowStageCoreHomology_stabilization_square R A q n) x
  have hε : ε.hom y = a := Iso.inv_hom_id_apply ε a
  have hMono : Mono ε.hom := inferInstance
  have hInjective : Function.Injective ε.hom :=
    (AddCommGrpCat.mono_iff_injective ε.hom).mp hMono
  apply hInjective
  change ε.hom (ε.inv b) = ε.hom ((finiteFreeRowRegularDenominator R) • y)
  calc
    _ = b := Iso.inv_hom_id_apply ε b
    _ = T a := hSquare.symm
    _ = T (ε.hom y) := congrArg T hε.symm
    _ = ε.hom ((finiteFreeRowRegularDenominator R) • y) :=
      (finiteFreeRowCoreRegularAction_eq R A q y).symm

end AlgebraicKTheory.StableGL
