/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeBimoduleTensorOperators
public import MathlibExt.CategoryTheory.NativeDerivedBifunctorSources

/-!
# Derived balanced tensor, module Hom and their original evaluation

The ordinary tensor is the actual middle-ring coequalizer. Its native
signed total cochains are derived along the original pair of Q functors.
Module Hom is the native right adjoint of that computed derived tensor.
The commuting outer ring action is retained throughout.

Source: DK arXiv:1311.2374v2, Sections 5.2, 8.2 and 9.1.
Native constructors: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache 2.0; credits remain in imported tensor/derived ports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeDerivedBimoduleOperators

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open NativeBimoduleTensorOperators NativeDerivedBifunctorSources NativeParametrizedAdjoints

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ R S : Mon C, Abelian (Bimod R S)]
  (R S T : Mon C)

local instance bimodulePreadditive (A B : Mon C) : Preadditive (Bimod A B) :=
  Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

variable [CochainSource (tensorModulesFlipped R S T)]
  (D : LeftDerivationSource (tensorModulesFlipped R S T))

/-- Actual derived tensor with the parameter order that retains the left R action. -/
def derivedTensorModules :
    DerivedCategory (Bimod S T) ⥤ DerivedCategory (Bimod R S) ⥤
      DerivedCategory (Bimod R T) :=
  derivedBifunctor (tensorModulesFlipped R S T) D

/-- Structural existence of right adjoints to that exact derived tensor. -/
structure DerivedModuleHomSource : Prop where
  closed : ∀ N : DerivedCategory (Bimod S T),
    ((derivedTensorModules R S T D).obj N).IsLeftAdjoint

/-- The original RHom over the right ring, with full native parameter mates. -/
def derivedModuleHom (H : DerivedModuleHomSource R S T D) :
    (DerivedCategory (Bimod S T))ᵒᵖ ⥤ DerivedCategory (Bimod R T) ⥤
      DerivedCategory (Bimod R S) :=
  letI := H.closed
  rightAdjointBifunctor (derivedTensorModules R S T D)

/-- Evaluation is the native counit of the same actual derived balanced tensor. -/
def derivedModuleEvaluation (H : DerivedModuleHomSource R S T D)
    (N : DerivedCategory (Bimod S T)) (L : DerivedCategory (Bimod R T)) :
    ((derivedTensorModules R S T D).obj N).obj
      (((derivedModuleHom R S T D H).obj (op N)).obj L) ⟶ L :=
  letI := H.closed
  (Adjunction.ofIsLeftAdjoint ((derivedTensorModules R S T D).obj N)).counit.app L

end MathlibExt.CategoryTheory.NativeDerivedBimoduleOperators
