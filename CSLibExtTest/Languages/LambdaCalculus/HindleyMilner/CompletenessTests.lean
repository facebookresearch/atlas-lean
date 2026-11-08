/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.HindleyMilner.Completeness

@[expose] public section

/-!
# Tests for completeness of Algorithm W

Principal types for closed expressions: success exactly on typable terms, the inferred type
of the identity generalizes `int → int`, and failure on λ-bound self-application is
equivalent to untypability.
-/

set_option autoImplicit false

namespace CSLibExtTest.Languages.LambdaCalculus.HindleyMilner.Completeness

open Cslib.Unification Cslib.Unification.Term Cslib.HindleyMilner

/-- Base types for the examples. -/
inductive Base where
  | int
  deriving DecidableEq, Repr

private def I : Expr := .lam "x" (.var "x")

/-- `I : int → int`, so W succeeds on `I`, and `int → int` is an instance of its answer. -/
example : ∃ τ, infer (B := Base) I = some τ ∧ ∃ r, node (const .int) (const .int) = τ.subst r := by
  refine infer_complete (HasType.lam ?_)
  have h := HasType.var (Γ := [("x", toScheme (const Base.int))]) (x := "x")
    (σ := toScheme (const Base.int)) (fun _ ↦ const .int) (by simp [Ctx.lookup])
  rwa [inst_toScheme] at h

/-- W fails on `λf. f f` because it has no type. -/
example : infer (B := Base) (.lam "f" (.app (.var "f") (.var "f"))) = none := by
  rw [← Option.not_isSome_iff_eq_none, infer_isSome_iff]
  rintro ⟨τ, h⟩
  exact not_hasType_lam_self_app [] "f" τ h

/-- Principality, as stated for any inference result. -/
example (e : Expr) (τ : Ty Base) (h : infer e = some τ) (τ' : Ty Base) (h' : HasType [] e τ') :
    ∃ r, τ' = τ.subst r :=
  (infer_principal h).2 τ' h'

end CSLibExtTest.Languages.LambdaCalculus.HindleyMilner.Completeness
