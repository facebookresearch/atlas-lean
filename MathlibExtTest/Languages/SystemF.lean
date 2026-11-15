/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Languages.SystemF

@[expose] public section

/-- The closed identity term at type `var 0 → var 0` (under one
type variable) is well typed. -/
theorem id_typed :
    HasType 1 [] (.lam (.var 0) (.var 0)) (.arr (.var 0) (.var 0)) :=
  HasType.lam (Δ := 1) (Γ := []) (by simp [TyWf])
    (HasType.var (Γ := [.var 0]) (k := 0) (T := .var 0) rfl
      (by simp [TyWf]))

/-- Boundary check: applying the identity at the function type
to the identity is well typed, and its beta reduct (the identity
itself) keeps the type, by subject reduction. -/
example :
    HasType 1 []
      (tmSubst 0 (.lam (.var 0) (.var 0)) (.var 0))
      (.arr (.var 0) (.var 0)) := by
  refine subject_reduction (T := .arr (.var 0) (.var 0)) ?_ (Step.beta (A := .arr (.var 0) (.var 0)) (t := .var 0) (u := .lam (.var 0) (.var 0)))
  exact HasType.app
    (HasType.lam (Δ := 1) (Γ := []) (by simp [TyWf])
      (HasType.var (Γ := [.arr (.var 0) (.var 0)]) (k := 0)
        (T := .arr (.var 0) (.var 0)) rfl (by simp [TyWf])))
    id_typed
