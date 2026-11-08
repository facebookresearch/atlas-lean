/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.HindleyMilner.AlgorithmW
public meta import CSLibExt.Languages.LambdaCalculus.HindleyMilner.AlgorithmW

@[expose] public section

/-!
# Tests for Algorithm W

Inferred types of the combinators `I`, `K`, `S` and `S K K`, polymorphic `let`, and the
failures: λ-bound self-application, the same program with `id` λ-bound instead of
`let`-bound, and an unbound variable. Then soundness applied to an inference result.
-/

set_option autoImplicit false

namespace CSLibExtTest.Languages.LambdaCalculus.HindleyMilner.AlgorithmW

open Cslib.Unification Cslib.Unification.Term Cslib.HindleyMilner

private def I : Expr := .lam "x" (.var "x")
private def K : Expr := .lam "x" (.lam "y" (.var "x"))
private def S : Expr :=
  .lam "x" (.lam "y" (.lam "z" (.app (.app (.var "x") (.var "z")) (.app (.var "y") (.var "z")))))

private def v (n : ℕ) : Ty Empty := var n

-- `I : α → α`, `K : α → β → α`
#guard infer (B := Empty) I == some (node (v 0) (v 0))
#guard infer (B := Empty) K == some (node (v 0) (node (v 1) (v 0)))
-- `S : (α → β → γ) → (α → β) → α → γ`
#guard infer (B := Empty) S == some (node (node (v 2) (node (v 4) (v 5)))
  (node (node (v 2) (v 4)) (node (v 2) (v 5))))
-- `S K K : α → α`
#guard infer (B := Empty) (.app (.app S K) K) == some (node (v 9) (v 9))
-- `let` makes `id` and `k` polymorphic
#guard infer (B := Empty) (.let_ "id" I (.app (.var "id") (.var "id"))) == some (node (v 2) (v 2))
#guard infer (B := Empty) (.let_ "k" K (.app (.app (.var "k") (.var "k")) I)) ==
  some (node (v 4) (node (v 5) (v 4)))
-- failures: self-application of a λ-bound variable (twice), an unbound variable
#guard (infer (B := Empty) (.lam "f" (.app (.var "f") (.var "f")))).isNone
#guard (infer (B := Empty) (.app (.lam "id" (.app (.var "id") (.var "id"))) I)).isNone
#guard (infer (B := Empty) (.var "y")).isNone

/-- Soundness turns any inference result into a typing derivation. -/
example (e : Expr) (τ : Ty Empty) (h : infer e = some τ) : HasType [] e τ :=
  hasType_of_infer_eq_some h

end CSLibExtTest.Languages.LambdaCalculus.HindleyMilner.AlgorithmW
