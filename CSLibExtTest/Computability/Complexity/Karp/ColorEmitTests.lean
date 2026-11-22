/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ColorEmit
public meta import CSLibExt.Computability.Complexity.Karp.ColorEmit

/-! Tests for the SAT-to-3-COLOR emitter machine. -/

namespace Cslib.Complexity.Karp.EmitColor.Tests

open Turing Cslib.CookLevin Cslib.Complexity.SatVerifier Cslib.Logic.PL

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
  let m : MS := ⟨(toks φ).reverse, o, 0, 0, [], [], [], [], 0, 0⟩
  let r := runF prog 1000000 0 ⟨some start, false, m.stk⟩
  (r.1.l, r.1.stk .O, r.2)

/-- The emitter halts at `done` with `toCol φ` on the output stack, within the step bound of
`run`. -/
private def check (φ : CNF) : Bool :=
  let r := emitOut φ
  r.1 == some .done && r.2.1 == toCol φ && decide (r.2.2 ≤ 500 * ((toks φ).length + 1) ^ 4)

-- The empty formula: the palette triangle on three vertices.
#guard check []
#guard (emitOut []).2.1 = encodeE 3 [(1, 2), (0, 2), (0, 1)]
-- The empty clause: a fourth vertex joined to the palette.
#guard check [[]]
#guard (emitOut [[]]).2.1 = encodeE 4 [(3, 2), (3, 1), (3, 0), (1, 2), (0, 2), (0, 1)]
#guard check [[], [(0, true)]]
-- The spec's formulas: a unit clause, two literals (one OR gadget), opposite and equal
-- occurrences of one variable in two clauses.
#guard check [[(0, true)]]
#guard check [[(1, true)]]
#guard check [[(1, true), (2, false)]]
#guard (emitOut [[(1, true), (2, false)]]).2.1 =
  encodeE 10 (colSt [[(1, true), (2, false)]]).em.reverse
#guard check [[(1, true)], [(1, false)]]
#guard check [[(1, true)], [(1, true)]]
-- Repeated variables with both polarities, within and across clauses.
#guard check [[(3, true), (3, true)], [(3, true), (3, false)], [(3, false)]]
#guard check [[(1, true), (1, false)], [(1, false), (2, true)], [(2, false), (1, true)]]
-- Variable 0 (empty name), long names sharing prefixes, empty clauses between others.
#guard check [[(0, false)], [(0, true), (5, false), (0, false)]]
#guard check [[(12, true), (3, false), (0, true)], [], [(7, true)], [(0, true), (0, false)]]
#guard check [[(4, true), (12, false)], [(12, true), (28, true)], [(4, false), (28, false)]]
-- The instance is pushed onto whatever the output stack already holds.
#guard (emitOut [[(1, true), (2, true)], [(2, false)]] [true, false]).2.1 =
  toCol [[(1, true), (2, true)], [(2, false)]] ++ [true, false]

end Cslib.Complexity.Karp.EmitColor.Tests
