/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Elaboration

/-!
# Consumer tests for STLC elaboration and NbE normalization

Executable examples for `elaborate`/`infer`/`check`/`normalizeRaw`:
successful elaboration of the identity, out-of-scope variables, applying a
base-typed term, argument-type mismatches, and beta/eta normalization
results computed by `normalizeRaw`.
-/

open scoped CslibStlc

namespace Cslib.Languages.LambdaCalculus.Stlc

namespace ElaborationTests

/-- The single base type used in these examples. -/
abbrev b : Ty Unit := .base ()

/-- The raw identity at `b`. -/
def rawId : RawTm Unit := .lam b (.var 0)

/-- Successful elaboration infers the identity type. -/
example : infer ([] : List (Ty Unit)) rawId = some (b ⇒ b) := by decide

/-- Elaborating an erased intrinsic term returns the same term. -/
example :
    elaborate ([] : List (Ty Unit)) (Tm.lam (Tm.var Var.zero) : Tm [] (b ⇒ b)).erase =
      some ⟨b ⇒ b, Tm.lam (Tm.var Var.zero)⟩ :=
  elaborate_erase _

/-- Checking succeeds at the inferred type and fails at a wrong type. -/
example : check ([] : List (Ty Unit)) rawId (b ⇒ b) = true := by decide

example : check ([] : List (Ty Unit)) rawId b = false := by decide

/-- An out-of-scope variable does not elaborate. -/
example : infer ([] : List (Ty Unit)) (.var 0) = none := by decide

example : infer ([b] : List (Ty Unit)) (.var 1) = none := by decide

/-- Applying a base-typed term does not elaborate. -/
example : infer ([b] : List (Ty Unit)) (.app (.var 0) (.var 0)) = none := by decide

/-- An argument of the wrong type does not elaborate: the function at index `1`
expects a `b ⇒ b` argument but receives the `b` at index `0`. -/
example : infer ([b, (b ⇒ b) ⇒ b] : List (Ty Unit)) (.app (.var 1) (.var 0)) = none := by
  decide

/-- The identity at the function type, used for a well-typed beta redex. -/
def rawId2 : RawTm Unit := .lam (b ⇒ b) (.var 0)

/-- Beta: normalizing `(λf. f) (λx. x)` gives the identity. -/
example : normalizeRaw ([] : List (Ty Unit)) (.app rawId2 rawId) = some ⟨b ⇒ b, rawId⟩ := by
  decide

/-- Eta: NbE normal forms are eta-long, so `λx. f x` is already normal. -/
example :
    normalizeRaw ([b ⇒ b] : List (Ty Unit)) (.lam b (.app (.var 1) (.var 0))) =
      some ⟨b ⇒ b, .lam b (.app (.var 1) (.var 0))⟩ := by
  decide

/-- Normalization preserves the inferred type on a concrete term. -/
example : infer ([] : List (Ty Unit)) (.app rawId2 rawId) = some (b ⇒ b) := by decide

end ElaborationTests

end Cslib.Languages.LambdaCalculus.Stlc
