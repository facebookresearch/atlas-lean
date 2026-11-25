/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensorRight
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.ResolutionComparison
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Derived bimodule tensor and Hom functors

The tensor–Hom adjunction produces right-module-valued Tor and Ext. Exact
forgetting compares these with the abelian-group derived models.
The scalar rings have independent universes and may be noncommutative;
the carrier universe is the common universe of the underived adjunction.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe r s v

namespace ModuleCat.BalancedTensorRight

private theorem forgetting_preservesHomology (T : Type r) [Ring T] :
    (forget₂ (ModuleCat.{v} T) AddCommGrpCat.{v}).PreservesHomology := by
  let U : ModuleCat.{v} T ⥤ AddCommGrpCat.{v} := forget₂ _ _
  let : PreservesLimits U :=
    ModuleCat.forget₂AddCommGroup_preservesLimits (R := T)
  let : PreservesFiniteLimits U :=
    CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits U
  let : PreservesFiniteColimits U := ⟨by
    intro J hJ hFin
    exact @ModuleCat.forget₂PreservesColimitsOfShape T _ J hJ
      (inferInstance : HasColimitsOfShape J AddCommGrpCat.{v})⟩
  exact CategoryTheory.Functor.preservesHomologyOfExact U

variable (R : Type r) (S : Type s) [Ring R] [Ring S]
  (B : Type v) [AddCommGroup B] [Module R B] [Module Sᵐᵒᵖ B]
  [SMulCommClass R Sᵐᵒᵖ B]

section Tor

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]

/-- Tor is the native left-derived actual tensor functor, with its right S-action. -/
def torFunctor (n : ℕ) : ModuleCat.{v} Rᵐᵒᵖ ⥤ ModuleCat.{v} Sᵐᵒᵖ :=
  (tensorFunctor R S B).leftDerived n

/-- Exact forgetting preserves the original native projective-resolution computation. -/
def torForgetIso (n : ℕ) :
    torFunctor R S B n ⋙ forget₂ (ModuleCat.{v} Sᵐᵒᵖ) AddCommGrpCat.{v} ≅
      (tensorFunctor R S B ⋙
        forget₂ (ModuleCat.{v} Sᵐᵒᵖ) AddCommGrpCat.{v}).leftDerived n := by
  letI : (forget₂ (ModuleCat.{v} Sᵐᵒᵖ) AddCommGrpCat.{v}).PreservesHomology := by
    exact forgetting_preservesHomology (T := Sᵐᵒᵖ)
  exact (tensorFunctor R S B).leftDerivedCompIsoOfPreservesHomology
    (forget₂ (ModuleCat.{v} Sᵐᵒᵖ) AddCommGrpCat.{v}) n

/-- The actual tensor adjunction gives the native S-linear degree-zero identification. -/
def torZeroIso : torFunctor R S B 0 ≅ tensorFunctor R S B :=
  (tensorFunctor R S B).leftDerivedZeroIsoSelf

/-- Its forward map is the existing native augmentation-induced map. -/
theorem torZeroIso_hom : (torZeroIso R S B).hom =
    (tensorFunctor R S B).fromLeftDerivedZero := rfl

end Tor

section Ext

variable [HasInjectiveResolutions (ModuleCat.{v} Sᵐᵒᵖ)]

/-- ExtS(B,-) is the native right-derived Hom functor, with its right R-action. -/
def extFunctor (n : ℕ) : ModuleCat.{v} Sᵐᵒᵖ ⥤ ModuleCat.{v} Rᵐᵒᵖ :=
  (homFunctor R S B).rightDerived n

/-- Exact forgetting preserves the native injective-resolution computation. -/
def extForgetIso (n : ℕ) :
    extFunctor R S B n ⋙ forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v} ≅
      (homFunctor R S B ⋙
        forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).rightDerived n := by
  letI : (forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}).PreservesHomology := by
    exact forgetting_preservesHomology (T := Rᵐᵒᵖ)
  exact (homFunctor R S B).rightDerivedCompIsoOfPreservesHomology
    (forget₂ (ModuleCat.{v} Rᵐᵒᵖ) AddCommGrpCat.{v}) n

/-- The actual right adjoint earns the native R-linear degree-zero Hom identification. -/
def extZeroIso : extFunctor R S B 0 ≅ homFunctor R S B := by
  letI : (homFunctor R S B).IsRightAdjoint :=
    ⟨tensorFunctor R S B, ⟨tensorAdjunction R S B⟩⟩
  exact (homFunctor R S B).rightDerivedZeroIsoSelf

end Ext

end ModuleCat.BalancedTensorRight
