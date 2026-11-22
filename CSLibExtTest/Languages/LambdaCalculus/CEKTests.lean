/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.CEK
import Mathlib.Logic.Relation

/-!
# Tests for the CEK machine

A complete run of `(λ. 0) (λ. 0)` that uses every transition rule, a lookup
at a nonzero index, a variable outside its environment with no successor,
and uses of `step_deterministic` and `ret_mt_terminal`.
-/

namespace Cslib.Languages.LambdaCalculus.CEKTests

open Cslib.Languages.LambdaCalculus.CEK

/-- The identity abstraction `λ. 0`. -/
def idTm : Tm := .lam (.var 0)

/-- The closure of the identity in the empty environment. -/
def idClos : Clos := .clos (.var 0) []

/-- `(λ. 0) (λ. 0)` runs to the identity closure under the empty
continuation by the rules `app`, `lam`, `arg`, `lam`, `fn`, and `var`. -/
example : Relation.ReflTransGen Step (.eval (.app idTm idTm) [] .mt)
    (.ret idClos .mt) :=
  .head Step.app <| .head Step.lam <| .head Step.arg <| .head Step.lam <|
    .head Step.fn <| .single (Step.var rfl)

/-- The first step of that run is the only one possible. -/
example (s : State) (h : Step (.eval (.app idTm idTm) [] .mt) s) :
    s = .eval idTm [] (.arg idTm [] .mt) :=
  step_deterministic h Step.app

/-- The run ends in a terminal state. -/
example (s : State) : ¬ Step (.ret idClos .mt) s :=
  ret_mt_terminal idClos s

/-- Index `1` returns the second closure of the environment, and nothing
else. -/
example (v w : Clos) (k : Kont) : Step (.eval (.var 1) [v, w] k) (.ret w k) :=
  Step.var rfl

example (v w : Clos) (k : Kont) (s : State)
    (h : Step (.eval (.var 1) [v, w] k) s) : s = .ret w k :=
  step_deterministic h (Step.var rfl)

/-- A variable whose index is outside its environment has no successor. -/
example (v : Clos) (k : Kont) (s : State) : ¬ Step (.eval (.var 1) [v] k) s := by
  intro h
  cases h with
  | var h => simp at h

/-- The function body runs in the closure's environment, not the caller's:
the argument value is pushed onto the closure environment `[w]`. -/
example (t : Tm) (w : Clos) (caller : List Clos) :
    Relation.ReflTransGen Step (.ret (.clos t [w]) (.arg (.lam (.var 0)) caller .mt))
      (.eval t [.clos (.var 0) caller, w] .mt) :=
  .head Step.arg <| .head Step.lam <| .single Step.fn

end Cslib.Languages.LambdaCalculus.CEKTests
