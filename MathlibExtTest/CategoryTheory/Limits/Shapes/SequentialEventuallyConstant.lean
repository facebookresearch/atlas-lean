/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module


public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialEventuallyConstant

/-!
# Stable-stage inverse-limit clients

These clients use eventual invertibility of successor maps to obtain a limit
and the comparison with a chosen stable stage.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor.SequentialEventuallyConstantTest

universe v u

variable {C : Type u} [Category.{v} C]
variable (A : ℕᵒᵖ ⥤ C) (N : ℕ)
variable (h : ∀ n : ℕ, N ≤ n →
  IsIso (A.map (homOfLE (Nat.le_succ n)).op))

example : A.IsEventuallyConstantTo (op N) :=
  isEventuallyConstantTo_op_of_eventually_transition_iso A N h

example : HasLimit A :=
  hasLimit_of_eventually_transition_iso A N h

section Limit

variable [HasLimit A]

example : limit A ≅ A.obj (op N) :=
  sequentialLimitIsoAtOfEventuallyTransitionIso A N h

example :
    (sequentialLimitIsoAtOfEventuallyTransitionIso A N h).hom =
      limit.π A (op N) :=
  sequentialLimitIsoAtOfEventuallyTransitionIso_hom A N h

end Limit

section Constant

variable (X : C)

example : HasLimit ((Functor.const ℕᵒᵖ).obj X) := by
  apply hasLimit_of_eventually_transition_iso
    ((Functor.const ℕᵒᵖ).obj X) 0
  intro n _
  change IsIso (𝟙 X)
  infer_instance

end Constant

end CategoryTheory.Functor.SequentialEventuallyConstantTest

end

#print axioms CategoryTheory.Functor.sequentialLimitIsoAtOfEventuallyTransitionIso
