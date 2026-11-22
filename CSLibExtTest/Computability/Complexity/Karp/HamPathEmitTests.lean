/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathEmit
public meta import CSLibExt.Computability.Complexity.Karp.HamPathEmit

/-! Tests for the SAT-to-HAMPATH emitter machine. -/

namespace Cslib.Complexity.Karp.EmitHam.Tests

open Turing Cslib.CookLevin Cslib.Complexity.SatVerifier Cslib.Logic.PL

/-- Step a `TM2` program, with fuel, until the next step would halt; return the last
configuration with a label and the number of steps taken. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ × ℕ
  | 0, n, c => (c, n)
  | f + 1, n, c => match TM2.step M c with
    | some c' => if c'.l.isSome then runF M f (n + 1) c' else (c, n)
    | none => (c, n)

/-- The initial stacks: the token stack of `φ`, the output stack `o`, the rest empty. -/
private def init (φ : CNF) (o : List Bool) : ∀ k, List (Γ k)
  | .T => (toks φ).reverse
  | .O => o
  | _ => []

/-- Run the emitter on `φ` with the output stack `o`; report the final label, the output stack
and the step count. -/
private def emitOut (φ : CNF) (o : List Bool := []) : Option Lab × List Bool × ℕ :=
  let r := runF prog 10000000 0 ⟨some start, false, init φ o⟩
  (r.1.l, r.1.stk .O, r.2)

/-- The emitter halts at `done` with `toHam φ` on the output stack, within the step bound of
`run`. -/
private def check (φ : CNF) : Bool :=
  let r := emitOut φ
  r.1 == some .done && r.2.1 == toHam φ && decide (r.2.2 ≤ 2000 * ((toks φ).length + 1) ^ 5)

-- The empty formula: one vertex, no arcs.
#guard check []
#guard (emitOut []).2.1 = Path.encodeP 0 0 1 []
-- An empty clause: no variables, so no diamonds.
#guard check [[]]
#guard check [[], []]
-- One literal, positive and negative.
#guard check [[(0, true)]]
#guard check [[(0, false)]]
#guard check [[(1, true)], [(1, false)]]
-- A tautological clause, and complementary unit clauses.
#guard check [[(0, true), (0, false)]]
#guard check [[(0, true)], [(0, false)]]
-- Repeated and sparse variable names, empty clauses in between.
#guard check [[(5, true)], [(2, false), (5, true)]]
#guard check [[(0, true), (1, false)], [(1, true)]]
#guard check [[(3, true), (3, true)], [(3, true), (3, false)], [(3, false)]]
#guard check [[(12, true), (3, false), (0, true)], [], [(7, true)], [(0, true), (0, false)]]
#guard check [[(4, true), (12, false)], [(12, true), (28, true)], [(4, false), (28, false)]]
#guard check [[(0, true), (1, true)], [(0, false), (1, false)], [(0, true), (1, false)]]
-- The instance is pushed onto whatever the output stack already holds.
#guard (emitOut [[(1, true), (2, true)], [(2, false)]] [true, false]).2.1 =
  toHam [[(1, true), (2, true)], [(2, false)]] ++ [true, false]
end Cslib.Complexity.Karp.EmitHam.Tests
