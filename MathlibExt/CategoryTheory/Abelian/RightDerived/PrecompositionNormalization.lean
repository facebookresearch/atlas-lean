/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaComparison
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
## The canonical zero normalization, outgoing extension, uniqueness and connector laws for the
right-derived precomposition comparison. The zero slots use the existing stock
rightDerivedZeroIsoSelf and its whiskering; their characteristic laws reuse the universal delta
API
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uA vA

namespace CategoryTheory.Functor.RightDerived

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (T : C ⥤ D) [T.Additive] [T.PreservesInjectiveObjects] [T.PreservesHomology]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
variable (B : D ⥤ A) [B.Additive] [PreservesFiniteLimits B]
variable {P : C ⥤ A} [P.Additive] [PreservesFiniteLimits P] (α : P ≅ T ⋙ B)

/-- The zero-degree identification of the source derived delta functor. -/
def precompSourceZeroIso : P.rightDerivedDeltaFunctor.T 0 ≅ P := P.rightDerivedZeroIsoSelf

/-- The zero-degree identification of the precomposed target delta functor. -/
def precompTargetZeroIso :
    (CohomologicalDeltaFunctor.precompose T (precompShortExact T) B.rightDerivedDeltaFunctor).T 0 ≅ T ⋙ B :=
  Functor.isoWhiskerLeft T B.rightDerivedZeroIsoSelf

/-- The precomposition delta map has the original normalized source and target zero maps. -/
theorem precompDeltaIsoOfIso_zero_normalization :
    CohomologicalDeltaFunctor.Hom.app (precompDeltaIsoOfIso T B α).hom 0 ≫
        (precompTargetZeroIso T B).hom = (precompSourceZeroIso (P := P)).hom ≫ α.hom := by
  apply NatTrans.ext
  funext X
  change (Functor.rightDerivedPrecompIsoOfIso T B α 0).hom.app X ≫
      B.rightDerivedZeroIsoSelf.hom.app (T.obj X) = P.rightDerivedZeroIsoSelf.hom.app X ≫ α.hom.app X
  exact Functor.rightDerivedPrecompIsoOfIso_zeroIsoSelf T B α X

/-- The precomposition delta map is the outgoing extension of its fixed zero map. -/
theorem precompDeltaIsoOfIso_normalizedExtension :
    (precompDeltaIsoOfIso T B α).hom =
      CohomologicalDeltaFunctor.normalizedExtension P.rightDerivedDeltaFunctor
        (CohomologicalDeltaFunctor.precompose T (precompShortExact T) B.rightDerivedDeltaFunctor)
        P.isUniversal_rightDerivedDeltaFunctor (precompSourceZeroIso (P := P))
        (precompTargetZeroIso T B) α.hom := by
  apply CohomologicalDeltaFunctor.hom_eq_of_app_zero _ P.isUniversal_rightDerivedDeltaFunctor _
  apply (cancel_mono (precompTargetZeroIso T B).hom).1
  exact (precompDeltaIsoOfIso_zero_normalization T B α).trans
    (CohomologicalDeltaFunctor.normalizedExtension_normalization _ _ P.isUniversal_rightDerivedDeltaFunctor
      (precompSourceZeroIso (P := P)) (precompTargetZeroIso T B) α.hom).symm

/-- The same zero normalization uniquely determines the full precomposition delta map. -/
theorem precompDeltaIsoOfIso_unique
    (f : P.rightDerivedDeltaFunctor ⟶
      CohomologicalDeltaFunctor.precompose T (precompShortExact T) B.rightDerivedDeltaFunctor)
    (h₀ : CohomologicalDeltaFunctor.Hom.app f 0 ≫ (precompTargetZeroIso T B).hom =
      (precompSourceZeroIso (P := P)).hom ≫ α.hom) :
    f = (precompDeltaIsoOfIso T B α).hom := by
  apply CohomologicalDeltaFunctor.hom_eq_of_app_zero _ P.isUniversal_rightDerivedDeltaFunctor _
  apply (cancel_mono (precompTargetZeroIso T B).hom).1
  exact h₀.trans (precompDeltaIsoOfIso_zero_normalization T B α).symm

omit [PreservesFiniteLimits P] [PreservesFiniteLimits B] in
/-- The fixed comparison intertwines the original and mapped connectors. -/
theorem canonicalConnecting_precompOfIso (n : ℕ) (S : ShortComplex.ShortExactSequences C) :
    (Functor.rightDerivedConnecting P n).app S ≫
      (Functor.rightDerivedPrecompIsoOfIso T B α (n + 1)).hom.app S.obj.X₁ =
    (Functor.rightDerivedPrecompIsoOfIso T B α n).hom.app S.obj.X₃ ≫
      (Functor.rightDerivedConnecting B n).app ⟨S.obj.map T, precompShortExact T S.obj S.property⟩ :=
  DeltaFunctor.System.comm (precompDeltaHomOfIso T B α).hom n S

/-- Evaluate the original and mapped canonical connector equation without changing its endpoints. -/
theorem canonicalConnecting_precompOfIso_value
    (T' : C ⥤ D) [T'.Additive] [T'.PreservesInjectiveObjects] [T'.PreservesHomology]
    [PreservesFiniteLimits T'] [PreservesFiniteColimits T']
    (B' : D ⥤ AddCommGrpCat.{vA}) [B'.Additive]
    {P' : C ⥤ AddCommGrpCat.{vA}} [P'.Additive] (α' : P' ≅ T' ⋙ B')
    (n : ℕ) (S : ShortComplex.ShortExactSequences C) (y : (P'.rightDerived n).obj S.obj.X₃) :
    (Functor.rightDerivedPrecompIsoOfIso T' B' α' (n + 1)).hom.app S.obj.X₁
        ((Functor.rightDerivedConnecting P' n).app S y) =
      (Functor.rightDerivedConnecting B' n).app ⟨S.obj.map T', precompShortExact T' S.obj S.property⟩
        ((Functor.rightDerivedPrecompIsoOfIso T' B' α' n).hom.app S.obj.X₃ y) := by
  let a := (Functor.rightDerivedConnecting P' n).app S
  let b := (Functor.rightDerivedPrecompIsoOfIso T' B' α' (n + 1)).hom.app S.obj.X₁
  let c := (Functor.rightDerivedPrecompIsoOfIso T' B' α' n).hom.app S.obj.X₃
  let d := (Functor.rightDerivedConnecting B' n).app
    ⟨S.obj.map T', precompShortExact T' S.obj S.property⟩
  have h := ConcreteCategory.congr_hom (canonicalConnecting_precompOfIso T' B' α' n S) y
  exact (ConcreteCategory.comp_apply a b y).symm.trans
    (h.trans (ConcreteCategory.comp_apply c d y))

/-- Paste an original connector square with its fixed comparison square on a class. -/
theorem pastedConnector_apply {H₃ H₁ G₃ G₁ B₃ B₁ : Type*}
    (e₃ : H₃ → G₃) (e₁ : H₁ → G₁) {c₃ : G₃ → B₃} {c₁ : G₁ → B₁}
    (δH : H₃ → H₁) {δG : G₃ → G₁} {δB : B₃ → B₁}
    (hG : ∀ x, δG (e₃ x) = e₁ (δH x)) (hC : ∀ y, c₁ (δG y) = δB (c₃ y)) (x : H₃) :
    δB (c₃ (e₃ x)) = c₁ (e₁ (δH x)) :=
  (hC (e₃ x)).symm.trans (congrArg c₁ (hG x))

end CategoryTheory.Functor.RightDerived
