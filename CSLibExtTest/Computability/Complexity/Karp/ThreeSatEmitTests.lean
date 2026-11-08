/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ThreeSatEmit
public meta import CSLibExt.Computability.Complexity.Karp.ThreeSatEmit

/-! Tests for the SAT-to-3SAT emitter machine. -/

namespace Cslib.Complexity.Karp.Emit3.Tests

open Turing Cslib.CookLevin Cslib.Complexity.SatVerifier Cslib.Logic.PL

/-- Step a `TM2` program, with fuel, until the next step would halt; return the last
configuration with a label and the number of steps taken. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ × ℕ
  | 0, n, c => (c, n)
  | f + 1, n, c => match TM2.step M c with
    | some c' => if c'.l.isSome then runF M f (n + 1) c' else (c, n)
    | none => (c, n)

/-- Run the emitter on `φ` from the token stack `(toks φ).reverse` and an empty output stack;
report the final label, the output stack and the step count. -/
private def emitOut (φ : CNF) : Option Lab × List Bool × ℕ :=
  let r := runF prog 100000 0 ⟨some start, false, st (toks φ).reverse [] 0 0⟩
  (r.1.l, r.1.stk .O, r.2)

/-- The emitter halts at `done` with `encodeCNF (to3 φ)` on the output stack, within the step
bound of `run`. -/
private def check (φ : CNF) : Bool :=
  let r := emitOut φ
  r.1 == some .done && r.2.1 == encodeCNF (to3 φ) &&
    decide (r.2.2 ≤ 8 * ((toks φ).length + 1) ^ 2)

-- The empty formula, an empty clause, a unit clause.
#guard check []
#guard check [[]]
#guard check [[(1, true)]]
#guard (emitOut [[(1, true)]]).2.1 = encodeCNF [[(2, true)]]
-- Clauses of length 2 and 4 become chains with fresh variables.
#guard check [[(1, true), (2, false)]]
#guard (emitOut [[(1, true), (2, false)]]).2.1 =
  encodeCNF [[(2, true), (fresh 0, true)], [(fresh 0, false), (4, false)]]
#guard check [[(1, true), (2, false), (3, true), (4, false)]]
-- Two clauses sharing a variable; fresh numbers continue across clauses.
#guard check [[(1, true), (2, false)], [(2, true), (3, true)]]
#guard check [[(1, true), (2, true), (3, false)], [(3, true), (1, false), (2, true)]]
-- Variable 0 (empty name), long names, and empty clauses between others.
#guard check [[(0, false)], [(0, true), (5, false), (0, false)]]
#guard check [[(12, true), (3, false), (0, true)], [], [(7, true)], [(0, true), (0, false)]]
-- The output is pushed onto whatever the output stack already holds.
#guard (runF prog 100000 0 ⟨some start, false,
    st (toks [[(1, true), (2, true)]]).reverse [true, false] 0 0⟩).1.stk .O =
  encodeCNF (to3 [[(1, true), (2, true)]]) ++ [true, false]

end Cslib.Complexity.Karp.Emit3.Tests
