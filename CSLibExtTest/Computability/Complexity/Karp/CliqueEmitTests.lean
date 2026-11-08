/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.CliqueEmit
public meta import CSLibExt.Computability.Complexity.Karp.CliqueEmit

/-! Tests for the SAT-to-CLIQUE emitter machine. -/

namespace Cslib.Complexity.Karp.EmitClique.Tests

open Turing Cslib.CookLevin Cslib.Complexity.SatVerifier Cslib.Logic.PL

/-- Step a `TM2` program, with fuel, until the next step would halt; return the last
configuration with a label and the number of steps taken. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ × ℕ
  | 0, n, c => (c, n)
  | f + 1, n, c => match TM2.step M c with
    | some c' => if c'.l.isSome then runF M f (n + 1) c' else (c, n)
    | none => (c, n)

/-- Run the emitter on `φ` from the token stack `(toks φ).reverse` and the output stack `o`;
report the final label, the output stack and the step count. -/
private def emitOut (φ : CNF) (o : List Bool := []) : Option Lab × List Bool × ℕ :=
  let r := runF prog 1000000 0 ⟨some start, false, st (toks φ).reverse o [] [] [] 0 0⟩
  (r.1.l, r.1.stk .O, r.2)

/-- The emitter halts at `done` with `toClique φ` on the output stack, within the step bound of
`run`. -/
private def check (φ : CNF) : Bool :=
  let r := emitOut φ
  r.1 == some .done && r.2.1 == toClique φ &&
    decide (r.2.2 ≤ 8 * ((toks φ).length + 1) ^ 3)

-- The empty formula: `k = 0` on the empty graph.
#guard check []
#guard (emitOut []).2.1 = encodeKG 0 0 []
-- An empty clause has no vertices.
#guard check [[]]
#guard check [[], [(0, true)]]
#guard (emitOut [[], [(0, true)]]).2.1 = encodeKG 2 1 []
-- One clause: its occurrences share the clause, so no edges.
#guard check [[(1, true)]]
#guard check [[(1, true), (2, false), (3, true)]]
#guard (emitOut [[(1, true), (2, false), (3, true)]]).2.1 = encodeKG 1 3 [false, false, false]
-- The spec's formula `(x₁ ∨ ¬x₂) ∧ ¬x₁`: only `¬x₂` and `¬x₁` are adjacent.
#guard check [[(1, true), (2, false)], [(1, false)]]
#guard (emitOut [[(1, true), (2, false)], [(1, false)]]).2.1 = encodeKG 2 3 [false, false, true]
-- Complementary pairs across clauses are not adjacent; equal literals are.
#guard check [[(1, true)], [(1, false)]]
#guard (emitOut [[(1, true)], [(1, false)]]).2.1 = encodeKG 2 2 [false]
#guard (emitOut [[(1, true)], [(1, true)]]).2.1 = encodeKG 2 2 [true]
#guard check [[(1, true), (1, false)], [(1, false), (2, true)], [(2, false), (1, true)]]
-- Repeated variables, within and across clauses.
#guard check [[(3, true), (3, true)], [(3, true), (3, false)], [(3, false)]]
-- Variable 0 (empty name), long names sharing prefixes, empty clauses between others.
#guard check [[(0, false)], [(0, true), (5, false), (0, false)]]
#guard check [[(12, true), (3, false), (0, true)], [], [(7, true)], [(0, true), (0, false)]]
#guard check [[(4, true), (12, false)], [(12, true), (28, true)], [(4, false), (28, false)]]
-- The instance is pushed onto whatever the output stack already holds.
#guard (emitOut [[(1, true), (2, true)], [(2, false)]] [true, false]).2.1 =
  toClique [[(1, true), (2, true)], [(2, false)]] ++ [true, false]

end Cslib.Complexity.Karp.EmitClique.Tests
