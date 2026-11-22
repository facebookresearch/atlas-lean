/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.LambdaCalculus.ClosureConversion.Flat

/-!
# Tests for flat closure conversion

* `λa. λb. λc. a`: the innermost closure captures only `a` (one environment
  entry, against two for whole-environment capture), and its code reads `a`
  from position `0` of that environment.
* `λx. λy. x x`: a variable used twice is captured once (`captured` removes
  duplicates).
* `(λx. λy. x) (λz. z)`: flat conversion, a target evaluation, and the relation
  of the results; the result closure's environment holds exactly the converted
  identity closure.
* Converted closed programs have closed code.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.ClosureConversion.FlatTests

open Target Target.Tm

abbrev T : Stlc.Ty Unit := .base ()

/-- `λa. λb. λc. a`. -/
def k3 : Stlc.RawTm Unit := .lam T (.lam T (.lam T (.var 2)))

/-- The innermost lambda `λc. a` (with `a` at index `2`) captures only `a`,
which is index `1` in its enclosing scope `[b, a]`. -/
example : captured (.var 2 : Stlc.RawTm Unit) = [1] := by decide

/-- Whole-environment capture would pack both `b` and `a`; flat capture packs
only `a`. -/
example : convertFlat (flatAcc [0]) (.lam T (.var 2) : Stlc.RawTm Unit) =
    .pair (.code (.fst (snds 0 (.snd (.var 0))))) (.pair (flatAcc [0] 1) .unit) := by
  decide

example : convertFlat (flatAcc [0]) (.lam T (.var 2) : Stlc.RawTm Unit) =
    .pair (.code (.fst (.snd (.var 0)))) (.pair (.fst (.snd (.var 0))) .unit) := by
  decide

/-- A variable used twice is captured once. -/
example : captured (.app (.var 1) (.var 1) : Stlc.RawTm Unit) = [0] := by decide

/-- `λz. z`. -/
def idTm : Stlc.RawTm Unit := .lam T (.var 0)

/-- `(λx. λy. x) (λz. z)`. -/
def constId : Stlc.RawTm Unit := .app (.lam T (.lam T (.var 1))) idTm

theorem constId_eval : Source.Eval [] constId (.clo (.var 1) [.clo (.var 0) []]) :=
  .app .lam .lam .lam

/-- The converted identity closure. -/
def idClosure : Value := .pair (.code (.fst (.var 0))) .unit

/-- The flat closure for `λy. x` with `x` bound to the identity: code
`fst (snd #0)` and the one-entry environment `(id, ())`. -/
def constClosure : Value :=
  .pair (.code (.fst (snds 0 (.snd (.var 0))))) (.pair idClosure .unit)

theorem constId_convert_eval : Eval [] (closureConvertFlat constId) constClosure := by
  refine .letIn (.pair .code .unit) (.app (.fst (.var rfl))
    (.pair (.pair .code .unit) (.snd (.var rfl))) ?_)
  exact .pair .code (.pair (.fst (.var rfl)) .unit)

theorem captured_var0 : captured (.var 0 : Stlc.RawTm Unit) = [] := by decide

theorem captured_var1 : captured (.var 1 : Stlc.RawTm Unit) = [0] := by decide

theorem idTm_rel : FlatValRel (.clo (.var 0 : Stlc.RawTm Unit) []) idClosure :=
  .clo (ws := []) (by decide) (fun k h => absurd h (by simp [captured_var0]))
    (fun k h => absurd h (by simp [captured_var0]))

example : FlatValRel (.clo (.var 1 : Stlc.RawTm Unit) [.clo (.var 0) []]) constClosure :=
  .clo (ws := [idClosure]) (by decide)
    (fun k h => by
      simp only [captured_var1, List.length_singleton, Nat.lt_one_iff] at h
      subst h
      simp [captured_var1])
    (fun k h₁ h₂ => by
      simp only [captured_var1, List.length_singleton, Nat.lt_one_iff] at h₁
      subst h₁
      simpa [captured_var1] using idTm_rel)

/-- The general theorem gives a related result for the closed program. -/
example : ∃ w, Eval [] (closureConvertFlat constId) w ∧
    FlatValRel (.clo (.var 1 : Stlc.RawTm Unit) [.clo (.var 0) []]) w :=
  closureConvertFlat_correct (by decide) constId_eval

/-- Converted closed programs have closed code. -/
example : Scoped 0 (closureConvertFlat k3) := closureConvertFlat_scoped (by decide)

end Cslib.Languages.LambdaCalculus.ClosureConversion.FlatTests
