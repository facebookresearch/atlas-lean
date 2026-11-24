/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Module.Opposite

/-!
# Opposite scalar actions for modules with commuting left actions

For an A-module whose original scalar operators commute, the same operators
through unop define a lawful A-opposite module. A itself may be noncommutative.
The only commutation premise is the existing SMulCommClass on the original
left action; no right action or target module certificate is supplied.
-/

@[expose] public section
set_option autoImplicit false

universe u v z

namespace Module

variable (A : Type u) [Semiring A] (M : Type v) [AddCommMonoid M]
  [Module A M] [SMulCommClass A A M]

/-- The original commuting scalar action defines a module over the opposite semiring. -/
@[instance_reducible]
def oppositeOfCommutingAction : Module Aᵐᵒᵖ M where
  smul a m := MulOpposite.unop a • m
  one_smul m := by
    change (1 : A) • m = m
    exact one_smul A m
  mul_smul a b m := by
    change (MulOpposite.unop b * MulOpposite.unop a) • m =
      MulOpposite.unop a • (MulOpposite.unop b • m)
    rw [mul_smul]
    exact smul_comm (MulOpposite.unop b) (MulOpposite.unop a) m
  smul_zero a := by
    change MulOpposite.unop a • (0 : M) = 0
    exact smul_zero (MulOpposite.unop a)
  smul_add a m n := by
    change MulOpposite.unop a • (m + n) =
      MulOpposite.unop a • m + MulOpposite.unop a • n
    exact smul_add (MulOpposite.unop a) m n
  add_smul a b m := by
    change (MulOpposite.unop a + MulOpposite.unop b) • m =
      MulOpposite.unop a • m + MulOpposite.unop b • m
    exact add_smul (MulOpposite.unop a) (MulOpposite.unop b) m
  zero_smul m := by
    change (0 : A) • m = 0
    exact zero_smul A m

/-- The canonical opposite scalar acts by its original unop scalar. -/
@[simp] theorem oppositeOfCommutingAction_smul (a : Aᵐᵒᵖ) (m : M) :
    (letI := oppositeOfCommutingAction A M; a • m) = MulOpposite.unop a • m :=
  rfl

/-- Every original commuting scalar action also commutes with the canonical opposite action. -/
theorem oppositeOfCommutingAction_smulComm {R : Type z}
    [SMul R M] [SMulCommClass R A M] :
    letI := oppositeOfCommutingAction A M
    SMulCommClass R Aᵐᵒᵖ M := by
  let := oppositeOfCommutingAction A M
  constructor
  intro r a m
  change r • (MulOpposite.unop a • m) = MulOpposite.unop a • (r • m)
  exact smul_comm r (MulOpposite.unop a) m

/-- The original and canonical opposite actions commute by the source scalar-commutation law. -/
theorem oppositeOfCommutingAction_actionsComm :
    letI := oppositeOfCommutingAction A M
    SMulCommClass A Aᵐᵒᵖ M :=
  oppositeOfCommutingAction_smulComm A M (R := A)

end Module
