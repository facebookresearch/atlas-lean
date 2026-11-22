/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.CliqueComplete
public meta import CSLibExt.Computability.Complexity.Karp.CliqueComplete

/-! Tests for the composed CLIQUE reduction machine: the SAT tokenizer followed by `EmitClique`. -/

namespace Cslib.Complexity.Karp.CliqueCompleteTests

open Turing Cslib.CookLevin Cslib.Logic.PL MetaMathlibExt.ComplexityTheory

/-- Step a `TM2` program, with fuel, until the next step would halt; return the last
configuration with a label and the number of steps taken. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ × ℕ
  | 0, n, c => (c, n)
  | f + 1, n, c => match TM2.step M c with
    | some c' => if c'.l.isSome then runF M f (n + 1) c' else (c, n)
    | none => (c, n)

/-- Run `TokThen.prog emitClique` on `x`: it ends at `fin` with `reduceClique x` on the output
stack, within the bound of `TokThen.run`. -/
private def check (x : List Bool) : Bool :=
  let E := emitClique
  let r := runF (TokThen.prog E) 400000 0 ⟨some (TokThen.start E), false, TokThen.init E x⟩
  (match r.1.l with | some (.inr (.inr true)) => true | _ => false) &&
    (r.1.stk (.inr E.cO)).map E.eO == reduceClique x &&
    decide (r.2 ≤ 2 * x.length + 3 + E.B x.length)

-- Decodable inputs: the empty formula, an empty clause, complementary and repeated literals.
#guard check (encodeCNF [])
#guard check (encodeCNF [[]])
#guard check (encodeCNF [[(1, true)], [(1, false)]])
#guard check (encodeCNF [[(1, true), (2, false)], [(2, true), (0, false)], [(1, true)]])
-- Undecodable inputs write the fixed no-instance `noKG`.
#guard check [true] && reduceClique [true] = noKG
#guard check [false, true, true]

-- The assembled statements elaborate.
example : IsPolyTime reduceClique := isPolyTime_reduceClique
example : cliqueDec ∈ NP := cliqueDec_mem_NP

end Cslib.Complexity.Karp.CliqueCompleteTests
