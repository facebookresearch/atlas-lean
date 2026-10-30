/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.ClosureConversion.Correctness

/-!
# Tests for closure conversion

* `(λx. x) (λy. y)`: the converted program, its target evaluation, and the
  relation between the source and target results.
* `(λx. λy. x) (λz. z)`: the result closure captures `x`; its converted code
  reads `x` from the environment (`fst (snd #0)`), and the captured environment
  holds the converted identity closure.
* `λx. (λy. y) x`: the shifted accessor under the `let` of an application,
  checked syntactically and by a target evaluation.
* `λx. λy. λz. x`: environment layout and accessor depth for nested closures.
* Converted programs are closed with closed code.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.ClosureConversion.Tests

open Target Target.Tm

/-- Base types do not matter for closure conversion; use `Unit`. -/
abbrev T : Stlc.Ty Unit := .base ()

/-- `λy. y`. -/
def idTm : Stlc.RawTm Unit := .lam T (.var 0)

/-- `(λx. x) (λy. y)`. -/
def idApp : Stlc.RawTm Unit := .app idTm idTm

theorem idApp_eval : Source.Eval [] idApp (.clo (.var 0) []) :=
  .app .lam .lam (.var rfl)

/-- The converted identity closure: code `fst #0` (return the argument) with the
empty environment. -/
def idClosure : Value := .pair (.code (.fst (.var 0))) .unit

example : closureConvert idApp =
    .letIn (.pair (.code (.fst (.var 0))) .unit)
      (.app (.fst (.var 0)) (.pair (.pair (.code (.fst (.var 0))) .unit) (.snd (.var 0)))) :=
  rfl

theorem idApp_target : Eval [] (closureConvert idApp) idClosure :=
  .letIn (.pair .code .unit)
    (.app (.fst (.var rfl)) (.pair (.pair .code .unit) (.snd (.var rfl))) (.fst (.var rfl)))

example : ValRel (.clo (.var 0) [] : Source.Value Unit) idClosure :=
  .clo (ws := []) rfl fun _ h => absurd h (Nat.not_lt_zero _)

/-- `λx. λy. x`. -/
def constTm : Stlc.RawTm Unit := .lam T (.lam T (.var 1))

/-- `(λx. λy. x) (λz. z)`, which returns a closure capturing `x`. -/
def constApp : Stlc.RawTm Unit := .app constTm idTm

theorem constApp_eval :
    Source.Eval [] constApp (.clo (.var 1) [.clo (.var 0) []]) :=
  .app .lam .lam .lam

/-- The converted result is a closure whose code reads the captured `x` from
its environment, and whose environment holds a value related to the identity
closure. -/
example : ∃ w ws, Eval [] (closureConvert constApp)
      (.pair (.code (.fst (.snd (.var 0)))) (encodeEnv ws)) ∧
      ws = [w] ∧ ValRel (.clo (.var 0) [] : Source.Value Unit) w := by
  obtain ⟨w, hw, hrel⟩ := closureConvert_correct constApp_eval
  cases hrel with
  | @clo _ _ ws hlen hrel =>
      match ws, hlen with
      | [w₀], _ =>
          exact ⟨w₀, [w₀], hw, rfl, hrel 0 (Nat.zero_lt_one) (Nat.zero_lt_one)⟩

theorem constApp_closed : constApp.Closed := by decide

/-- The converted program is closed and all its code is closed. -/
example : Scoped 0 (closureConvert constApp) := closureConvert_scoped constApp_closed

/-- `λx. (λy. y) x`: an application inside a lambda. Under the inserted `let`,
the argument `x` is fetched with the shifted accessor `fst #1`. -/
def etaId : Stlc.RawTm Unit := .lam T (.app idTm (.var 0))

example : closureConvert etaId =
    .pair (.code (.letIn (.pair (.code (.fst (.var 0))) (.pair (.fst (.var 0)) .unit))
      (.app (.fst (.var 0)) (.pair (.fst (.var 1)) (.snd (.var 0)))))) .unit :=
  rfl

/-- Running `(λx. (λy. y) x) (λz. z)` end to end in the target: the shifted
accessor fetches the argument, and the result is the converted identity
closure, as in the source. -/
example : Source.Eval [] (.app etaId idTm) (.clo (.var 0) []) :=
  .app .lam .lam (.app .lam (.var rfl) (.var rfl))

example : Eval [] (closureConvert (.app etaId idTm)) idClosure :=
  .letIn (.pair .code .unit)
    (.app (.fst (.var rfl)) (.pair (.pair .code .unit) (.snd (.var rfl)))
      (.letIn (.pair .code (.pair (.fst (.var rfl)) .unit))
        (.app (.fst (.var rfl)) (.pair (.fst (.var rfl)) (.snd (.var rfl))) (.fst (.var rfl)))))

/-- `λx. λy. λz. x`: the innermost code reads `x` from the second slot of its
environment, `fst (snd (snd #0))`, and each closure packs every variable in
scope. -/
def proj3 : Stlc.RawTm Unit := .lam T (.lam T (.lam T (.var 2)))

example : closureConvert proj3 =
    .pair (.code (.pair
      (.code (.pair (.code (.fst (.snd (.snd (.var 0)))))
        (.pair (.fst (.var 0)) (.pair (.fst (.snd (.var 0))) .unit))))
      (.pair (.fst (.var 0)) .unit))) .unit :=
  rfl

/-- A source variable out of scope does not evaluate; the scoping hypothesis
of `closureConvert_scoped` matters: `convert` maps it to an unbound target
variable. -/
example : ¬ Scoped 0 (closureConvert (.var 0 : Stlc.RawTm Unit)) := by
  intro h
  cases h with
  | var h => exact absurd h (Nat.not_lt_zero 0)

end Cslib.Languages.LambdaCalculus.ClosureConversion.Tests
