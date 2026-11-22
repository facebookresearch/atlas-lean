/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete
public meta import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete

/-! Tests for `TokThen`: the SAT tokenizer followed by an emitter, run as one machine. -/

namespace Cslib.Complexity.Karp.TokThenTests

open Turing Cslib.CookLevin Cslib.Logic.PL MetaMathlibExt.ComplexityTheory

/-- Step a `TM2` program, with fuel, until the next step would halt; return the last
configuration with a label and the number of steps taken. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ × ℕ
  | 0, n, c => (c, n)
  | f + 1, n, c => match TM2.step M c with
    | some c' => if c'.l.isSome then runF M f (n + 1) c' else (c, n)
    | none => (c, n)

/-- The 3SAT emitter with a non-empty output for undecodable input, so that branch is visible. -/
private abbrev emitN : Emitter := { emit3 with noOut := [true, false, false] }

/-- Run `TokThen.prog E` on `x`: it ends at `fin` with `out E x` (here `o`) on the output stack,
within `2 |x| + 3 + E.B |x|` steps (`TokThen.run`). -/
private def check (E : Emitter) (x o : List Bool) : Bool :=
  let r := runF (TokThen.prog E) 200000 0 ⟨some (TokThen.start E), false, TokThen.init E x⟩
  (match r.1.l with | some (.inr (.inr true)) => true | _ => false) &&
    (r.1.stk (.inr E.cO)).map E.eO == o && decide (r.2 ≤ 2 * x.length + 3 + E.B x.length)

-- Decodable inputs: the output is `encodeCNF (to3 φ)`, in order.
#guard check emit3 (encodeCNF []) (encodeCNF (to3 []))
#guard check emit3 (encodeCNF [[]]) (encodeCNF (to3 [[]]))
#guard check emit3 (encodeCNF [[(1, true)]]) (encodeCNF [[(2, true)]])
#guard check emit3 (encodeCNF [[(1, true), (2, false)], [(0, false)]])
  (encodeCNF (to3 [[(1, true), (2, false)], [(0, false)]]))
#guard check emit3 (encodeCNF [[(0, true), (1, false), (2, true), (3, false)]])
  (encodeCNF (to3 [[(0, true), (1, false), (2, true), (3, false)]]))
-- The output agrees with `reduce3` (decodable inputs) and with `noOut` (undecodable ones).
#guard check emitN (encodeCNF [[(1, false)]]) (reduce3 (encodeCNF [[(1, false)]]))
#guard check emitN [true] [true, false, false]
#guard check emitN [false, true, true] [true, false, false]
#guard check emit3 [true] []
#guard decodeCNF [true] = none && decodeCNF [false, true, true] = none

-- The public API elaborates for a concrete emitter.
example : IsPolyTime (TokThen.out emit3) := by
  rw [show TokThen.out emit3 = reduce3 from funext out_emit3]
  exact isPolyTime_reduce3

end Cslib.Complexity.Karp.TokThenTests
