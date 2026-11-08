/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.OneHot
public meta import CSLibExt.Computability.Complexity.CookLevin.OneHot

/-! Tests for the Cook-Levin clause generators: each machine, run to halting on a small
instance, leaves exactly the encoded clause family on its output stack.

`runF` steps a `TM2` program until it halts (or the fuel runs out); the checks are evaluated
with `#guard`. -/

namespace Cslib.Complexity.CookLevin.Tests

open Turing MetaMathlibExt Cslib.Complexity.DenseSAT Cslib.Complexity.CookLevin

/-- Step a `TM2` program until it halts, with fuel. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ
  | 0, c => c
  | n + 1, c => match TM2.step M c with
    | some c' => runF M n c'
    | none => c

/-! ### The transition family -/

/-- Two label/state codes, one stack, two symbol codes, window depth one. -/
private def L0 : Family.Layout := ⟨2, 1, 2, 1⟩

-- One situation (`0 ↦ 1`, reading symbol code `1`), one step, height one: a single clause
-- `¬X[0,0] ∨ ¬C[0,0,0,1] ∨ X[1,1]` over `2 · (2 + 2) = 8` variables.
#guard Family.family L0 (fun _ => 0) (fun _ => 1) (fun _ _ _ => 1) 1 1 1 =
  [[some false, none, none, some false, none, some true, none, none]]

#guard (runF (Family.prog L0 (fun _ => 0) (fun _ => 1) (fun _ _ _ => 1) 1) 100000
    ⟨some (.pre .eg), false, CounterView.st (Family.initF 1 1) []⟩).stk .out =
  encodeCNF (Family.family L0 (fun _ => 0) (fun _ => 1) (fun _ _ _ => 1) 1 1 1)

-- Two situations with different tables, two steps, height two: the runtime loop over `t`
-- and the label chain over `i` both run; existing output is kept below the formula.
#guard (runF (Family.prog L0 (fun i => i % 2) (fun i => (i + 1) % 2) (fun i _ _ => i % 2) 2)
      100000 ⟨some (.pre .eg), false, CounterView.st (Family.initF 2 2) [true]⟩).stk .out =
  encodeCNF (Family.family L0 (fun i => i % 2) (fun i => (i + 1) % 2) (fun i _ _ => i % 2) 2 2 2)
    ++ [true]

-- The machine halts within the fuel.
#guard (runF (Family.prog L0 (fun _ => 0) (fun _ => 1) (fun _ _ _ => 1) 1) 100000
    ⟨some (.pre .eg), false, CounterView.st (Family.initF 1 1) []⟩).l = none

/-! ### The cell one-hot family -/

-- Two symbol codes, one stack, `T = 1`, `H = 1`: two cells, each with one at-least-one clause
-- and one at-most-one clause.
#guard (OneHot.ohFamily L0 1 1).length = 4

#guard (runF (OneHot.prog L0) 100000
    ⟨some (.pre .inc), false, CounterView.st (OneHot.initF 1 1) []⟩).stk .out =
  encodeCNF (OneHot.ohFamily L0 1 1)

-- Three symbol codes, two stacks, height two.
#guard (runF (OneHot.prog ⟨1, 2, 3, 1⟩) 1000000
    ⟨some (.pre .inc), false, CounterView.st (OneHot.initF 1 2) []⟩).stk .out =
  encodeCNF (OneHot.ohFamily ⟨1, 2, 3, 1⟩ 1 2)

end Cslib.Complexity.CookLevin.Tests
