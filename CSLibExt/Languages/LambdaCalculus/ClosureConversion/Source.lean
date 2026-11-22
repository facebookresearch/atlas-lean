/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Closure conversion: source environment semantics
-/
module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Elaboration

/-!
# Environment semantics for raw lambda terms

The source language of closure conversion is the raw de Bruijn syntax
`Stlc.RawTm` of `../DeBruijn/Stlc/Elaboration.lean`, read as an untyped
call-by-value lambda calculus (binder annotations are ignored). Its semantics
is the standard big-step environment semantics: a lambda evaluates to a
closure pairing its body with the current environment, and an application runs
the closure body in the closure's environment extended with the argument.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.ClosureConversion

universe u

variable {Base : Type u}

namespace Source

/-- Source values: closures of a lambda body and its environment. -/
inductive Value (Base : Type u) where
  | clo : Stlc.RawTm Base → List (Value Base) → Value Base

/-- Big-step call-by-value environment semantics: `Eval ρ t v` when `t`
evaluates to `v` in environment `ρ` (index `0` first). -/
inductive Eval : List (Value Base) → Stlc.RawTm Base → Value Base → Prop
  | var {ρ : List (Value Base)} {n : Nat} {v : Value Base} (h : ρ[n]? = some v) :
      Eval ρ (.var n) v
  | lam {ρ : List (Value Base)} {A : Stlc.Ty Base} {body : Stlc.RawTm Base} :
      Eval ρ (.lam A body) (.clo body ρ)
  | app {ρ ρ' : List (Value Base)} {f a body : Stlc.RawTm Base} {v w : Value Base}
      (hf : Eval ρ f (.clo body ρ')) (ha : Eval ρ a v) (hbody : Eval (v :: ρ') body w) :
      Eval ρ (.app f a) w

/-- Source evaluation is deterministic. -/
theorem Eval.deterministic {ρ : List (Value Base)} {t : Stlc.RawTm Base} {v w : Value Base}
    (hv : Eval ρ t v) (hw : Eval ρ t w) : v = w := by
  induction hv generalizing w with
  | var h =>
      cases hw with
      | var h' => rw [h] at h'; exact Option.some.inj h'
  | lam => cases hw; rfl
  | app _ _ _ ihf iha ihb =>
      cases hw with
      | app hf' ha' hb' =>
          cases ihf hf'
          cases iha ha'
          exact ihb hb'

end Source

end Cslib.Languages.LambdaCalculus.ClosureConversion
