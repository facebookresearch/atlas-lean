/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeDerivedBimoduleOperators
public import MathlibExt.CategoryTheory.NativeBoundedBimoduleModels

/-!
# Structural source packaging for the original derived bimodule calculus

Every operation below is the native balanced tensor or its chosen native
right adjoint, derived from the prescribed signed cochain action.
Source: DK1311.2374v2 Sections4.10,5.2,8.2,9.1; Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite NativeBimoduleTensorOperators NativeDerivedBifunctorSources
open NativeDerivedBimoduleOperators
open NativeParametrizedAdjoints

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ R S : Mon C, Abelian (Bimod R S)] (R S T : Mon C)

local instance calculusPreadditive (A B : Mon C) : Preadditive (Bimod A B) :=
  Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

class TensorDerivationSource where
  [cochain : CochainSource (tensorModulesFlipped R S T)]
  derivation : LeftDerivationSource (tensorModulesFlipped R S T)

attribute [instance] TensorDerivationSource.cochain

variable [D : TensorDerivationSource R S T]

abbrev tensorDerived : DerivedCategory (Bimod S T) ⥤ DerivedCategory (Bimod R S) ⥤
    DerivedCategory (Bimod R T) :=
  derivedTensorModules R S T D.derivation

class TensorHomSource : Prop where
  closed : DerivedModuleHomSource R S T D.derivation

variable [H : TensorHomSource R S T]

abbrev homDerived : (DerivedCategory (Bimod S T))ᵒᵖ ⥤ DerivedCategory (Bimod R T) ⥤
    DerivedCategory (Bimod R S) :=
  derivedModuleHom R S T D.derivation H.closed

def evaluation (N : DerivedCategory (Bimod S T)) (L : DerivedCategory (Bimod R T)) :
    ((tensorDerived R S T).obj N).obj (((homDerived R S T).obj (op N)).obj L) ⟶ L :=
  derivedModuleEvaluation R S T D.derivation H.closed N L

class LeftTensorDerivationSource where
  [cochain : CochainSource (tensorModules R S T)]
  derivation : LeftDerivationSource (tensorModules R S T)

attribute [instance] LeftTensorDerivationSource.cochain

variable [L : LeftTensorDerivationSource R S T]

/-- The same native balanced tensor, derived in its original left-module parameter order. -/
abbrev tensorDerivedLeft : DerivedCategory (Bimod R S) ⥤ DerivedCategory (Bimod S T) ⥤
    DerivedCategory (Bimod R T) := derivedBifunctor (tensorModules R S T) L.derivation

class LeftTensorHomSource : Prop where
  closed : ∀ M : DerivedCategory (Bimod R S), ((tensorDerivedLeft R S T).obj M).IsLeftAdjoint

variable [LH : LeftTensorHomSource R S T]

/-- RHom for original left R-modules, retaining the right T action of the endpoint. -/
abbrev homLeftDerived : (DerivedCategory (Bimod R S))ᵒᵖ ⥤ DerivedCategory (Bimod R T) ⥤
    DerivedCategory (Bimod S T) :=
  letI := LH.closed
  rightAdjointBifunctor (tensorDerivedLeft R S T)

/-- Original left-module evaluation is this native counit in the endpoint module category. -/
def evaluationLeft (M : DerivedCategory (Bimod R S)) (O : DerivedCategory (Bimod R T)) :
    ((tensorDerivedLeft R S T).obj M).obj (((homLeftDerived R S T).obj (op M)).obj O) ⟶ O :=
  letI := LH.closed
  (Adjunction.ofIsLeftAdjoint ((tensorDerivedLeft R S T).obj M)).counit.app O

end MathlibExt.CategoryTheory.NativeDerivedBimoduleCalculus
