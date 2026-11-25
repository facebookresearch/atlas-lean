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

/-- **Source values of closure conversion.** A source value is a closure of a raw term $b$ (the
body of a lambda) over an environment $\rho$, which is a list of source values. -/
inductive Value (Base : Type u) where
  | clo : Stlc.RawTm Base → List (Value Base) → Value Base

/-- **Big-step semantics of the closure-conversion source.** Evaluation
$\rho \vdash t \Downarrow v$ of a raw term $t$ to a source value $v$ in an environment $\rho$ (a
list of source values, where variable $n$ refers to the entry of $\rho$ at index $n$, counting
from $0$) is the least relation closed under the following rules, a call-by-value environment
semantics that ignores the type annotations of lambdas. A variable $n$ evaluates to the entry of
$\rho$ at index $n$, when that entry exists. A lambda $\lambda. b$ evaluates to the closure of $b$
over $\rho$. If $f$ evaluates in $\rho$ to the closure of $b$ over $\rho'$, if
$\rho \vdash a \Downarrow v$, and if $v :: \rho' \vdash b \Downarrow w$, where $v :: \rho'$ is
$\rho'$ with $v$ added at index $0$, then $\rho \vdash f\,a \Downarrow w$. -/
inductive Eval : List (Value Base) → Stlc.RawTm Base → Value Base → Prop
  | var {ρ : List (Value Base)} {n : Nat} {v : Value Base} (h : ρ[n]? = some v) :
      Eval ρ (.var n) v
  | lam {ρ : List (Value Base)} {A : Stlc.Ty Base} {body : Stlc.RawTm Base} :
      Eval ρ (.lam A body) (.clo body ρ)
  | app {ρ ρ' : List (Value Base)} {f a body : Stlc.RawTm Base} {v w : Value Base}
      (hf : Eval ρ f (.clo body ρ')) (ha : Eval ρ a v) (hbody : Eval (v :: ρ') body w) :
      Eval ρ (.app f a) w

/-- **Source evaluation is deterministic.** For every environment $\rho$ of source values and
every raw term $t$, if $t$ evaluates in $\rho$ to source values $v$ and $w$, then $v = w$. -/
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
