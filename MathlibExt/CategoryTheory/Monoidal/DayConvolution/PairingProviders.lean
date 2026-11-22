/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.DayConvolution.MonoidLax

/-!
# Kan-extension and pairing data for Day convolution

Packages the pointwise Kan extensions and tensor-preservation data for the tensor, unit
and their mixed or iterated index shapes. A supplied Day monoidal structure determines
the full pairing family on its tensor.
-/

set_option autoImplicit false
noncomputable section

namespace CategoryTheory.MonoidalCategory.DayFunctor

open CategoryTheory CategoryTheory.Functor Limits MonoidalCategory
open scoped ExternalProduct
universe uV vV uC vC
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C] [MonoidalCategory C]

/-- The complete original Day construction providers with their input domains. -/
structure PairingProviders (C : Type uC) [Category.{vC} C] [MonoidalCategory C] where
  tensorExtensions : ∀ (F G : C ⥤ V), (tensor C).HasPointwiseLeftKanExtension (F ⊠ G)
  unitExtensions : (Functor.fromPUnit.{0} (𝟙_ C)).HasPointwiseLeftKanExtension
    (Functor.fromPUnit.{0} (𝟙_ V))
  leftTensor : ∀ (X : V) (d : C), PreservesColimitsOfShape
    (CostructuredArrow (tensor C) d) (tensorLeft X)
  rightTensor : ∀ (X : V) (d : C), PreservesColimitsOfShape
    (CostructuredArrow (tensor C) d) (tensorRight X)
  leftUnit : ∀ (X : V) (d : C), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorLeft X)
  rightUnit : ∀ (X : V) (d : C), PreservesColimitsOfShape
    (CostructuredArrow (Functor.fromPUnit.{0} (𝟙_ C)) d) (tensorRight X)
  rightMixedUnit : ∀ (X : V) (d : C × C), PreservesColimitsOfShape
    (CostructuredArrow ((𝟭 C).prod (Functor.fromPUnit.{0} (𝟙_ C))) d) (tensorRight X)
  rightTriple : ∀ (X : V) (d : C × C), PreservesColimitsOfShape
    (CostructuredArrow ((tensor C).prod (𝟭 C)) d) (tensorRight X)

/-- The full pairing family on the supplied Day tensor. -/
def PairingFamily (m : MonoidalCategory (DayFunctor C V)) : Type _ :=
  letI := m
  ∀ F G : DayFunctor C V, F.functor ⊠ G.functor ⟶ tensor C ⋙ (F ⊗ G).functor

end CategoryTheory.MonoidalCategory.DayFunctor
