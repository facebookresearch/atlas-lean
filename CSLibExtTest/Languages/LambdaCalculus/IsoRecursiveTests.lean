/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.IsoRecursive

/-!
# Tests for iso-recursive types

* Term substitution under a nested `lam` leaves the inner bound variable alone,
  shifts the substituted term, and lowers free variables; beta reduction uses it.
  Substitution at a nonzero index replaces exactly that variable.
* Type substitution under a nested `mu` leaves the inner bound variable alone,
  shifts the substituted type, and lowers free variables, also at a nonzero
  index.
* Unfolding a recursive type, and `progress` on a closed `unfold (fold unit)`.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.IsoRecursive.Tests

/-- The unit term is a value. -/
example : Value Tm.unit := Value.unit

/-- Unfolding a folded unit steps to the unit. -/
example : Step (Tm.unfold (Tm.fold Tm.unit)) Tm.unit :=
  Step.unfoldFold Value.unit

/-! ### Term substitution -/

/-- `(λ. λ. 0) unit` reduces to `λ. 0`: the inner bound variable is kept. -/
example : Step (.app (.lam (.lam (.var 0))) .unit) (.lam (.var 0)) :=
  Step.beta Value.unit

/-- `(λ. λ. 1) (λ. 0)` reduces to `λ. λ. 0`: the outer variable is replaced. -/
example :
    Step (.app (.lam (.lam (.var 1))) (.lam (.var 0))) (.lam (.lam (.var 0))) :=
  Step.beta (Value.lam _)

/-- Substituting the free variable `0` under a `lam` shifts it to `1`. -/
example : Tm.subst (.lam (.var 1)) (.var 0) = .lam (.var 1) := by decide

/-- Free variables above the substituted one are lowered, also under `lam`. -/
example : Tm.subst (.app (.var 3) (.lam (.var 2))) .unit =
    .app (.var 2) (.lam (.var 1)) := by decide

/-- Substituting `var 0` for index `1` in `var 1` gives `var 0`. -/
example : Tm.substAt (.var 1) 1 (.var 0) = .var 0 := by decide

/-- At index `1`, variable `0` is kept and variable `2` is lowered. -/
example : Tm.substAt (.app (.var 0) (.var 2)) 1 .unit =
    .app (.var 0) (.var 1) := by decide

/-- At index `1` under a `lam`, the target is `var 2` and the substituted
`var 0` becomes `var 1`. -/
example : Tm.substAt (.lam (.app (.var 2) (.var 1))) 1 (.var 0) =
    .lam (.app (.var 1) (.var 1)) := by decide

/-! ### Type substitution -/

/-- The inner bound variable of `μ. 0` is kept. -/
example : Ty.subst (.mu (.var 0)) .unit = .mu (.var 0) := by decide

/-- The outer variable under `mu` is replaced. -/
example : Ty.subst (.mu (.arr (.var 1) (.var 0))) .unit =
    .mu (.arr .unit (.var 0)) := by decide

/-- A substituted free type variable is shifted under `mu`. -/
example : Ty.subst (.mu (.var 1)) (.var 0) = .mu (.var 1) := by decide

/-- Free type variables above the substituted one are lowered. -/
example : Ty.subst (.arr (.var 2) (.mu (.var 3))) .unit =
    .arr (.var 1) (.mu (.var 2)) := by decide

/-- Substituting `var 0` for index `1` in `var 1` gives `var 0`. -/
example : Ty.substAt (.var 1) 1 (.var 0) = .var 0 := by decide

/-- At index `1` under a `mu`, the target is `var 2`, the substituted `var 0`
becomes `var 1`, and `var 3` is lowered to `var 2`. -/
example : Ty.substAt (.mu (.arr (.var 2) (.var 3))) 1 (.var 0) =
    .mu (.arr (.var 1) (.var 2)) := by decide

/-- Unfolding `μX. X → unit` gives `(μX. X → unit) → unit`. -/
example : Ty.unfold (.arr (.var 0) .unit) =
    .arr (.mu (.arr (.var 0) .unit)) .unit := by decide

/-! ### Progress -/

/-- `unfold (fold unit)` is closed and well typed at `unit`, through `μX. unit`. -/
theorem unfold_fold_unit_hasType : HasType [] (.unfold (.fold .unit)) .unit :=
  HasType.unfold (a := .unit) (HasType.fold HasType.unit)

example : Value (.unfold (.fold .unit)) ∨ ∃ t', Step (.unfold (.fold .unit)) t' :=
  progress unfold_fold_unit_hasType

end Cslib.Languages.LambdaCalculus.IsoRecursive.Tests
