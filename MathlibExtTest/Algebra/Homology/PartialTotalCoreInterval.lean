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

public import MathlibExt.Algebra.Homology.PartialTotalCoreInterval

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

local notation "core" =>
  CategoryTheory.Abelian.SpectralObject.coreE₁IncreasingHomologicalNat

example (q : ℕ) :
    CategoryTheory.ComposableArrows.mk₁
        (B.partialTotalEIntFiltration.map
          (homOfLE ((core).le₁₂ (0, q)))) ≅
      CategoryTheory.ComposableArrows.mk₁
        (B.partialTotalStepShortComplex 0).f :=
  B.partialTotalE₁StepIsoZero q

example (m q : ℕ) :
    CategoryTheory.ComposableArrows.mk₁
        (B.partialTotalEIntFiltration.map
          (homOfLE ((core).le₁₂ (m + 1, q)))) ≅
      CategoryTheory.ComposableArrows.mk₁
        (B.partialTotalStepShortComplex (m + 1)).f :=
  B.partialTotalE₁StepIsoSucc m q

example (p q : ℕ) :
    HEq ((B.partialTotalE₁StepIso p q).app 1)
      (B.partialTotalEIntFiltrationObjIso p) :=
  B.partialTotalE₁StepIso_app_one_heq p q

example (q : ℕ) :
    (B.partialTotalE₁StepIso 0 q).app 1 =
      B.partialTotalEIntFiltrationObjIso 0 :=
  eq_of_heq (B.partialTotalE₁StepIso_app_one_heq 0 q)

section Abelian

variable {D : Type u} [Category.{v} D] [Abelian D]

variable (B' : HomologicalComplex₂ D (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example (q : ℕ) :
    CategoryTheory.ComposableArrows.mk₁ (C := CochainComplex D ℤ)
        (B'.partialTotalCochainFiltration.map
          (homOfLE ((core).le₁₂ (0, q)))) ≅
      CategoryTheory.ComposableArrows.mk₁ (C := CochainComplex D ℤ)
        (B'.partialTotalStepCochainShortComplex 0).f :=
  B'.partialTotalE₁CochainStepIso 0 q

example (m q : ℕ) :
    CategoryTheory.ComposableArrows.mk₁ (C := CochainComplex D ℤ)
        (B'.partialTotalCochainFiltration.map
          (homOfLE ((core).le₁₂ (m + 1, q)))) ≅
      CategoryTheory.ComposableArrows.mk₁ (C := CochainComplex D ℤ)
        (B'.partialTotalStepCochainShortComplex (m + 1)).f :=
  B'.partialTotalE₁CochainStepIso (m + 1) q

end Abelian

end HomologicalComplex₂

end
