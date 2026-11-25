/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Monoidal.Mod.Closed
import Mathlib.Algebra.Polynomial.Basic

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe v u

namespace MathlibExtTest.CategoryTheory.Mod.Closed

section PublicSurface

#check Mod.evaluation
#check Mod.coevaluation
#check Mod.relativeTensorInternalHomAdjunction
#check Mod.instMonoidalClosed

#check @Mod.evaluation.{1, 1}
#check @Mod.evaluation.{0, 0}
#check @Mod.coevaluation.{1, 1}
#check @Mod.coevaluation.{0, 0}
#check @Mod.relativeTensorInternalHomAdjunction.{1, 1}
#check @Mod.relativeTensorInternalHomAdjunction.{0, 0}
#check @Mod.instMonoidalClosed.{1, 1}
#check @Mod.instMonoidalClosed.{0, 0}

end PublicSurface

section BraidedAdjunction

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C]
variable (A : CommMon C)
variable [HasCoequalizers C]
variable [HasEqualizers C]

example (M : Mod C A.X) :
    Mod.internalHomOfEqualizer A M ⋙ (Mod.relativeTensor A).obj M ⟶
      𝟭 (Mod C A.X) :=
  Mod.evaluation A M

example (M : Mod C A.X) :
    𝟭 (Mod C A.X) ⟶
      (Mod.relativeTensor A).obj M ⋙ Mod.internalHomOfEqualizer A M :=
  Mod.coevaluation A M

example (M : Mod C A.X) :
    (Mod.relativeTensor A).obj M ⊣ Mod.internalHomOfEqualizer A M :=
  Mod.relativeTensorInternalHomAdjunction A M

example (M : Mod C A.X) :
    (Mod.relativeTensorInternalHomAdjunction A M).unit =
      Mod.coevaluation A M := rfl

example (M : Mod C A.X) :
    (Mod.relativeTensorInternalHomAdjunction A M).counit =
      Mod.evaluation A M := rfl

example (M N : Mod C A.X) :
    ((Mod.relativeTensor A).obj M).map ((Mod.coevaluation A M).app N) ≫
        (Mod.evaluation A M).app
          (((Mod.relativeTensor A).obj M).obj N) =
      𝟙 (((Mod.relativeTensor A).obj M).obj N) :=
  (Mod.relativeTensorInternalHomAdjunction A M).left_triangle_components N

example (M N : Mod C A.X) :
    (Mod.coevaluation A M).app ((Mod.internalHomOfEqualizer A M).obj N) ≫
        (Mod.internalHomOfEqualizer A M).map ((Mod.evaluation A M).app N) =
      𝟙 ((Mod.internalHomOfEqualizer A M).obj N) :=
  (Mod.relativeTensorInternalHomAdjunction A M).right_triangle_components N

section Installed

local instance : MonoidalCategory (Mod C A.X) :=
  Mod.instMonoidalCategory A
local instance : MonoidalClosed (Mod C A.X) :=
  Mod.instMonoidalClosed A

example (M : Mod C A.X) : ihom M = Mod.internalHomOfEqualizer A M := rfl

example (M : Mod C A.X) :
    ihom.ev M = Mod.evaluation A M := rfl

example (M : Mod C A.X) :
    ihom.coev M = Mod.coevaluation A M := rfl

example (M N : Mod C A.X) :
    (M ◁ (ihom.coev M).app N) ≫
        (ihom.ev M).app (M ⊗ N) = 𝟙 (M ⊗ N) :=
  ihom.ev_coev M N

example (M N : Mod C A.X) :
    (ihom.coev M).app (M ⟶[Mod C A.X] N) ≫
        (ihom M).map ((ihom.ev M).app N) =
      𝟙 (M ⟶[Mod C A.X] N) :=
  ihom.coev_ev M N

example : Mod C A.X :=
  (ihom (Mod.regular A.X)).obj (Mod.regular A.X)

end Installed

end BraidedAdjunction

section SymmetricConsumer

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [SymmetricCategory C] [MonoidalClosed C]
variable (A : CommMon C)
variable [HasCoequalizers C]
variable [HasEqualizers C]

local instance : MonoidalCategory (Mod C A.X) :=
  Mod.instMonoidalCategory A
local instance : SymmetricCategory (Mod C A.X) :=
  Mod.instSymmetricCategory A
local instance : MonoidalClosed (Mod C A.X) :=
  Mod.instMonoidalClosed A

example (M : Mod C A.X) : ihom M = Mod.internalHomOfEqualizer A M := rfl

example (M : Mod C A.X) :
    ihom.ev M = Mod.evaluation A M := rfl

example (M : Mod C A.X) :
    ihom.coev M = Mod.coevaluation A M := rfl

end SymmetricConsumer

section TwoScalars

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C]
variable [HasCoequalizers C]
variable [HasEqualizers C]

example (A B : CommMon C) (M : Mod C A.X) (N : Mod C B.X) :
    ((Mod.relativeTensor A).obj M ⊣ Mod.internalHomOfEqualizer A M) ×
      ((Mod.relativeTensor B).obj N ⊣ Mod.internalHomOfEqualizer B N) :=
  (Mod.relativeTensorInternalHomAdjunction A M,
    Mod.relativeTensorInternalHomAdjunction B N)

example (A B : CommMon C) :
    @MonoidalClosed (Mod C A.X) _ (Mod.instMonoidalCategory A) ×
      @MonoidalClosed (Mod C B.X) _ (Mod.instMonoidalCategory B) :=
  (Mod.instMonoidalClosed A, Mod.instMonoidalClosed B)

end TwoScalars

section NoGlobalInstances

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [SymmetricCategory C] [MonoidalClosed C]
variable [HasCoequalizers C]
variable [HasEqualizers C]

example (_A : CommMon C) : True := by
  fail_if_success
    let _ : MonoidalCategory (Mod C _A.X) := inferInstance
  fail_if_success
    let _ : SymmetricCategory (Mod C _A.X) := inferInstance
  fail_if_success
    let _ : MonoidalClosed (Mod C _A.X) := inferInstance
  trivial

end NoGlobalInstances

section MissingClosed

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C]
variable (A : CommMon C)
variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
variable [HasEqualizers C]

example (_M : Mod C A.X) : True := by
  fail_if_success let _ := Mod.evaluation A _M
  fail_if_success let _ := Mod.coevaluation A _M
  fail_if_success let _ := Mod.relativeTensorInternalHomAdjunction A _M
  fail_if_success let _ := Mod.instMonoidalClosed A
  trivial

end MissingClosed

section MissingEqualizers

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C]
variable (A : CommMon C)
variable [HasCoequalizers C]

example (_M : Mod C A.X) : True := by
  fail_if_success let _ := Mod.evaluation A _M
  fail_if_success let _ := Mod.coevaluation A _M
  fail_if_success let _ := Mod.relativeTensorInternalHomAdjunction A _M
  fail_if_success let _ := Mod.instMonoidalClosed A
  trivial

end MissingEqualizers

section MissingCoequalizers

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C]
variable (A : CommMon C) [HasEqualizers C]

example (_M : Mod C A.X) : True := by
  fail_if_success let _ := Mod.evaluation A _M
  fail_if_success let _ := Mod.coevaluation A _M
  fail_if_success let _ := Mod.relativeTensorInternalHomAdjunction A _M
  fail_if_success let _ := Mod.instMonoidalClosed A
  trivial

end MissingCoequalizers

section InferredPreservation

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C]
variable (A : CommMon C) [HasEqualizers C] [HasCoequalizers C]

example (X : C) : PreservesColimitsOfSize.{0, 0} (tensorLeft X) :=
  inferInstance

example (X : C) : PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
  inferInstance

example : @MonoidalClosed (Mod C A.X) _ (Mod.instMonoidalCategory A) :=
  Mod.instMonoidalClosed A

end InferredPreservation

section PolynomialFalsifiers

open Polynomial

example :
    (fun p : Polynomial ℤ => C (p.coeff 0)) (X * 1) ≠
      X * (fun p : Polynomial ℤ => C (p.coeff 0)) 1 := by
  simpa using (X_ne_zero (R := ℤ)).symm

example :
    (∀ m a n : Polynomial ℤ,
      C (((m * a) * n).coeff 0) = C ((m * (a * n)).coeff 0)) ∧
    C (((X * 1) * 1 : Polynomial ℤ).coeff 0) ≠
      X * C (((1 : Polynomial ℤ) * 1).coeff 0) := by
  constructor
  · intro m a n
    rw [_root_.mul_assoc m a n]
  · simpa using (X_ne_zero (R := ℤ)).symm

end PolynomialFalsifiers

#print axioms Mod.evaluation
#print axioms Mod.coevaluation
#print axioms Mod.relativeTensorInternalHomAdjunction
#print axioms Mod.instMonoidalClosed

end MathlibExtTest.CategoryTheory.Mod.Closed
