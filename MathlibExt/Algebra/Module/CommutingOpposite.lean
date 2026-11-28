/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Module.Opposite

/-!
# Opposite actions from commuting scalar operators

For a semiring `A` and an `A`-semimodule `M`, assume the operators `a • -` commute with one
another. Then `a_op • m=unop(a_op) • m` defines an action of the opposite semiring `Aᵐᵒᵖ` on
`M`.

An additional action commuting with the `A`-action also commutes with this opposite action. In
particular, the two `A` and `Aᵐᵒᵖ` actions commute.
-/

@[expose] public section
set_option autoImplicit false

universe u v z

namespace Module

variable (A : Type u) [Semiring A] (M : Type v) [AddCommMonoid M]
  [Module A M] [SMulCommClass A A M]

/-- Let `A` be a semiring and `M` an `A`-semimodule whose scalar operators commute: `a • (b • m)=b
• (a • m)` for all `a,b,m`. The module structure `oppositeOfCommutingAction A M : Module Aᵐᵒᵖ
M` uses `a_op • m=MulOpposite.unop a_op • m`. -/
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

/-- Let `A` be a semiring and `M` an `A`-semimodule whose scalar operators commute: `a • (b • m)=b
• (a • m)` for all `a,b,m`. For `a_op : Aᵐᵒᵖ` and `m : M`, the constructed action satisfies
`a_op • m=MulOpposite.unop a_op • m`. -/
@[simp] theorem oppositeOfCommutingAction_smul (a : Aᵐᵒᵖ) (m : M) :
    (letI := oppositeOfCommutingAction A M; a • m) = MulOpposite.unop a • m :=
  rfl

/-- Let `A` be a semiring and `M` an `A`-semimodule whose scalar operators commute: `a • (b • m)=b
• (a • m)` for all `a,b,m`. Let a type `R` act on `M` with `SMulCommClass R A M`. Under the
constructed opposite action, `SMulCommClass R Aᵐᵒᵖ M` holds: `r • (a_op • m)=a_op • (r • m)`. -/
theorem oppositeOfCommutingAction_smulComm {R : Type z}
    [SMul R M] [SMulCommClass R A M] :
    letI := oppositeOfCommutingAction A M
    SMulCommClass R Aᵐᵒᵖ M := by
  let := oppositeOfCommutingAction A M
  constructor
  intro r a m
  change r • (MulOpposite.unop a • m) = MulOpposite.unop a • (r • m)
  exact smul_comm r (MulOpposite.unop a) m

/-- Let `A` be a semiring and `M` an `A`-semimodule whose scalar operators commute: `a • (b • m)=b
• (a • m)` for all `a,b,m`. For the constructed `Aᵐᵒᵖ`-action, `SMulCommClass A Aᵐᵒᵖ M` holds. -/
theorem oppositeOfCommutingAction_actionsComm :
    letI := oppositeOfCommutingAction A M
    SMulCommClass A Aᵐᵒᵖ M :=
  oppositeOfCommutingAction_smulComm A M (R := A)

end Module
