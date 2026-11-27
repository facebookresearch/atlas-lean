/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
public import MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
public import MathlibExt.CategoryTheory.NativeEnhancedBimoduleQuotients

/-!
# Native O-tempered, O-enhanced, Omega, DR, Sol and duality expressions

These are computed algebraic expressions, used with the actual Ind
coefficient category, beta differential rings, source distribution and
projective exponential objects. Analytic carrier construction is separate.
No realization functor or final reconstruction morphism is a field here.
DR is covariant balanced D-tensor. Sol is the contravariant native module
Hom into the right-local enhanced O representative. All shifts occur in
the original native derived category before the source quotient.

Source: DK1311.2374v2 Definitions5.2.1,8.2.1,9.1.1 and Section2.5;
Mathlib56a005 native tensor, Hom, shifts, adjoints and Q, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeEnhancedDModuleExpressions

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite NativeDerivedBimoduleCalculus NativeBoundedBimoduleModels
open NativeRingedAdjointImageModels NativeEnhancedBimoduleQuotients

universe u v uA vA uE vE
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ R S : Mon C, Abelian (Bimod R S)]

local instance expressionPreadditive (R S : Mon C) : Preadditive (Bimod R S) :=
  Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

section Tempered

variable (DX K DbarOp : Mon C)
  [TensorDerivationSource DX K DbarOp] [TensorHomSource DX K DbarOp]

/-- RHom over Dbar of the actual ordinary conjugate O and actual tempered distribution bimodule. -/
def temperedHolomorphic (conjugateO : DerivedCategory (Bimod K DbarOp))
    (temperedDistributions : DerivedCategory (Bimod DX DbarOp)) :
    DerivedCategory (Bimod DX K) :=
  ((homDerived DX K DbarOp).obj (op conjugateO)).obj temperedDistributions

end Tempered

section EnhancedO

variable (DX K DPop : Mon C)
  [TensorDerivationSource DX K DPop] [TensorHomSource DX K DPop]

/-- Product tau-Hom retains X as the commuting outer action. -/
def productTauHom (exponentialPlus : DerivedCategory (Bimod K DPop))
    (productTemperedO : DerivedCategory (Bimod DX DPop)) : DerivedCategory (Bimod DX K) :=
  ((homDerived DX K DPop).obj (op exponentialPlus)).obj productTemperedO

variable {Ambient : Type uA} [Category.{vA} Ambient]
  (graphProperImage : Ambient ⥤ DerivedCategory (Bimod DX K))
  [graphProperImage.IsLeftAdjoint]

/-- i! is the native right adjoint of the actual ringed graph proper image. -/
def graphExceptionalImage : DerivedCategory (Bimod DX K) ⥤ Ambient :=
  graphProperImage.rightAdjoint

end EnhancedO

section RealAmbient

variable (DX K : Mon C)
  (tauHomImage : DerivedCategory (Bimod DX K))

/-- The native Hom representative of O^E has the original source shift [2]. -/
def enhancedORaw : DerivedCategory (Bimod DX K) :=
  (shiftFunctor (DerivedCategory (Bimod DX K)) (2 : ℤ)).obj tauHomImage

/-- The native balanced right-exp(-tau) representative has the original source shift [1]. -/
def enhancedORightRaw (rightExponentialTensorImage : DerivedCategory (Bimod DX K)) :
    DerivedCategory (Bimod DX K) :=
  (shiftFunctor (DerivedCategory (Bimod DX K)) (1 : ℤ)).obj rightExponentialTensorImage

end RealAmbient

section Omega

variable (DX DXop K : Mon C) [TensorDerivationSource DXop DX K]
  (topformTransfer : DerivedCategory (Bimod DXop DX))
  (rightView : DerivedCategory (Bimod DXop K) ⥤ DerivedCategory (Bimod K DX))

/-- Omega^E is the actual top-form transfer tensor, followed by the elementary right-module view. -/
def enhancedOmegaRaw (enhancedORepresentative : DerivedCategory (Bimod DX K)) :
    DerivedCategory (Bimod K DX) :=
  rightView.obj (((tensorDerived DXop DX K).obj enhancedORepresentative).obj topformTransfer)

end Omega

section DR

variable (DX K : Mon C) [TensorDerivationSource K DX K]
  {A : Type uA} [Category.{vA} A] (ordinaryBetaPull : A ⥤ DerivedCategory (Bimod DX K))
  (omegaEnhanced : DerivedCategory (Bimod K DX))

/-- Covariant de Rham is the native Omega^E balanced tensor with the actual beta-pulled module. -/
def enhancedDRRaw : A ⥤ DerivedCategory (Bimod K K) where
  obj M := ((tensorDerived K DX K).obj (ordinaryBetaPull.obj M)).obj omegaEnhanced
  map f := ((tensorDerived K DX K).map (ordinaryBetaPull.map f)).app omegaEnhanced
  map_id M := by
    rw [ordinaryBetaPull.map_id, (tensorDerived K DX K).map_id]
    rfl
  map_comp f g := by
    rw [ordinaryBetaPull.map_comp, (tensorDerived K DX K).map_comp]
    rfl

end DR

section Sol

variable (DXop K : Mon C) [TensorDerivationSource K K DXop] [TensorHomSource K K DXop]
  {A : Type uA} [Category.{vA} A] (ordinaryRightBetaPull : A ⥤ DerivedCategory (Bimod K DXop))
  (rightLocalEnhancedO : DerivedCategory (Bimod K DXop))

/-- Contravariant solutions use the actual module Hom into R_D^E O^E. -/
def enhancedSolRaw : Aᵒᵖ ⥤ DerivedCategory (Bimod K K) :=
  ordinaryRightBetaPull.op ⋙ homDerived K K DXop ⋙
    (evaluation (DerivedCategory (Bimod K DXop)) (DerivedCategory (Bimod K K))).obj
      rightLocalEnhancedO

/-- Evaluation is the original module-Hom counit, before any coefficient or enhanced quotient. -/
def solutionEvaluation (M : A) :
    ((tensorDerived K K DXop).obj (ordinaryRightBetaPull.obj M)).obj
      ((enhancedSolRaw DXop K ordinaryRightBetaPull rightLocalEnhancedO).obj (op M)) ⟶
        rightLocalEnhancedO :=
  NativeDerivedBimoduleCalculus.evaluation K K DXop (ordinaryRightBetaPull.obj M) rightLocalEnhancedO

end Sol

section Duality

variable (DX DXop K : Mon C)
  [TensorDerivationSource DXop K DXop] [TensorHomSource DXop K DXop]
  [TensorDerivationSource DX DXop K]
  (inverseTopformTransfer : DerivedCategory (Bimod DX DXop))
  {A : Type uA} [Category.{vA} A] (ordinaryRightBetaPull : A ⥤ DerivedCategory (Bimod K DXop))

/-- Native duality uses the actual regular D bimodule, the inverse top-form transfer and [dim X]. -/
def dualObject (dim : ℕ) (M : A) : DerivedCategory (Bimod DX K) :=
  let rightDual := ((homDerived DXop K DXop).obj (op (ordinaryRightBetaPull.obj M))).obj
    ((DerivedCategory.singleFunctor (Bimod DXop DXop) 0).obj (Bimod.regular DXop))
  (shiftFunctor (DerivedCategory (Bimod DX K)) (dim : ℤ)).obj
    (((tensorDerived DX DXop K).obj rightDual).obj inverseTopformTransfer)

end Duality
end MathlibExt.CategoryTheory.NativeEnhancedDModuleExpressions
