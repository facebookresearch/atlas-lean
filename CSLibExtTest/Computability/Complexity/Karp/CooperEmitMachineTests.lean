/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.CooperEmitMachine
public meta import CSLibExt.Computability.Complexity.Karp.CooperEmitMachine

/-! Tests for the Cooper emitter machine. -/

namespace Cslib.Complexity.Karp.EmitCooper.Tests


open Turing Cslib.CookLevin Cslib.Complexity.SatVerifier Cslib.Logic.LegacyPL
  Cslib.Complexity.Cooper


/-- Step a `TM2` program, with fuel, until the next step would halt; return the last
configuration with a label and the number of steps taken. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ × ℕ
  | 0, n, c => (c, n)
  | f + 1, n, c => match TM2.step M c with
    | some c' => if c'.l.isSome then runF M f (n + 1) c' else (c, n)
    | none => (c, n)


/-- Run the emitter on `φ` from the token stack `(toks φ).reverse` and the output stack `o`,
every other stack empty; report the final label, the output stack and the step count. -/
private def emitOut (φ : CNF) (o : List Bool := []) : Option Lab × List Bool × ℕ :=
  let m : MS := ⟨(toks φ).reverse, o, 0, 0, 0, 0, [], [], [], []⟩
  let r := runF prog 1000000 0 ⟨some start, false, m.stk⟩
  (r.1.l, r.1.stk .O, r.2)


/-- The emitter halts at `done` with the code of Cooper's network of `φ` on the output stack,
within the step bound of `run`. -/
private def check (φ : CNF) : Bool :=
  let r := emitOut φ
  r.1 == some .done && r.2.1 == encodeRatNet (cooperNet φ) &&
    decide (r.2.2 ≤ 500 * ((toks φ).length + 1) ^ 4)


/-! ### Fixed formulas -/

/-- The empty formula: node `0` alone. -/
example : check [] = true := by
  decide +kernel


/-- One empty clause: its constant-false node, closed by an AND node. -/
example : check [[]] = true := by
  decide +kernel


/-- Variable `0`, whose name is the empty bit string. -/
example : check [[(0, true)]] = true := by
  decide +kernel


/-- Cooper's example `3SAT_ex`. -/
example : check cooperEx = true := by
  decide +kernel


/-- The unsatisfiable control. -/
example : check cooperUnsat = true := by
  decide +kernel


/-- A variable and its negation in one clause: the second literal finds the first one's root. -/
example : check [[(1, true), (1, false)]] = true := by
  decide +kernel


/-- Repeated variables within and across clauses. -/
example : check [[(3, true), (3, true)], [(3, true), (3, false)], [(3, false)]] = true := by
  decide +kernel


/-- Four clauses, one of them empty, with the variables `0` and `5` repeated across clauses. -/
example : check [[(0, true), (3, false)], [], [(0, false), (5, true)],
    [(5, false), (0, true), (2, true)]] = true := by
  decide +kernel


/-- Names that share a prefix, with an empty clause between two others. -/
example : check [[(12, true), (3, false), (0, true)], [], [(7, true)], [(0, true), (0, false)]] =
    true := by
  decide +kernel


/-- A twenty-bit name, repeated in the next clause. -/
example : check [[(1000003, true)], [(1000003, false), (2, true)]] = true := by
  decide +kernel


/-- The code is pushed onto whatever the output stack already holds. -/
example : (emitOut [[(1, true), (2, true)], [(2, false)]] [true, false]).2.1 =
    encodeRatNet (cooperNet [[(1, true), (2, true)], [(2, false)]]) ++ [true, false] := by
  decide +kernel

/-- The same run also halts at `done` within the step bound. -/
example : (emitOut [[(1, true), (2, true)], [(2, false)]] [true, false]).1 = some .done ∧
    (emitOut [[(1, true), (2, true)], [(2, false)]] [true, false]).2.2 ≤
      500 * ((toks [[(1, true), (2, true)], [(2, false)]]).length + 1) ^ 4 := by
  decide +kernel


/-! ### The emitter on bit strings -/

/-- A truncated string goes to the code of the fixed no-instance. -/
example : TokThen.out emitCooper [true] = encodeRatNet noBN := by
  decide +kernel


/-- The code of Cooper's example goes to the code of its network. -/
example : TokThen.out emitCooper (encodeCNF cooperEx) = encodeRatNet (cooperNet cooperEx) := by
  decide +kernel


/-! ### The main statements at full type -/

/-- The Cooper emitter computes Cooper's reduction map on every bit string. -/
example (x : List Bool) :
    Cslib.Complexity.Karp.TokThen.out Cslib.Complexity.Karp.emitCooper x =
      Cslib.Complexity.Cooper.reduceBN x := by
  exact Cslib.Complexity.Karp.out_emitCooper x


/-- Cooper's reduction map is polynomial-time. -/
example : MetaMathlibExt.ComplexityTheory.IsPolyTime Cslib.Complexity.Cooper.reduceBN := by
  exact Cslib.Complexity.Karp.isPolyTime_reduceBN


end Cslib.Complexity.Karp.EmitCooper.Tests
