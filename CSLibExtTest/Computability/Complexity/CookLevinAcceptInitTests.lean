/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.Assembly
public meta import CSLibExt.Computability.Complexity.CookLevin.Assembly

/-! Tests for the Cook-Levin accept and init generators: run to halting on small instances, each
leaves exactly the encoded clause family on its output stack. -/

namespace Cslib.Complexity.CookLevin.Tests

open Turing MetaMathlibExt Cslib.Complexity.DenseSAT Cslib.Complexity.CookLevin

/-- Step a `TM2` program until it halts, with fuel. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ
  | 0, c => c
  | n + 1, c => match TM2.step M c with
    | some c' => runF M n c'
    | none => c

/-- Two label/state codes, one stack, two symbol codes, window depth one. -/
private def L0 : Family.Layout := ⟨2, 1, 2, 1⟩

/-- As `L0`, with three symbol codes. -/
private def L1 : Family.Layout := ⟨2, 1, 3, 1⟩

/-! ### The accept family -/

-- Two codes, accepting code `1`, output stack `0` holding symbol code `1`: four unit clauses.
#guard (Accept.accFam L0 2 1 0 1 1 1).length = 4

#guard (runF (Accept.prog L0 2 1 0 1) 1000000
    ⟨some (.pre .eg), false, CounterView.st (Accept.initF 1 1) []⟩).stk .out =
  encodeCNF (Accept.accFam L0 2 1 0 1 1 1)

#guard (runF (Accept.prog L0 2 0 0 1) 1000000
    ⟨some (.pre .eg), false, CounterView.st (Accept.initF 2 2) [true]⟩).stk .out =
  encodeCNF (Accept.accFam L0 2 0 0 1 2 2) ++ [true]

/-! ### The init family -/

-- Input codes `[1, 0]`, certificate symbol code `1`, `m = 3`, `T = 1`, `H = 4`: the generator
-- reads the reversed input codes from its input stack. Certificate codes are increasing and
-- nonzero, as `InitFamily.ycs` produces them.
#guard (runF (InitFamily.iprog L0 0 0 [1]) 1000000
    ⟨some (.pre1 .eg), false,
      InitFamily.emb (CounterView.st (InitFamily.initF 1 2 1 1) [])
        ([⟨1, by decide⟩, ⟨0, by decide⟩] : List (Fin L0.g)).reverse⟩).stk (.b .out) =
  encodeCNF (InitFamily.initFam L0 0 0 [1] [⟨1, by decide⟩, ⟨0, by decide⟩] 3 1 4)

-- Empty input, three symbol codes, two certificate symbol codes.
#guard (runF (InitFamily.iprog L1 1 0 [1, 2]) 1000000
    ⟨some (.pre1 .eg), false,
      InitFamily.emb (CounterView.st (InitFamily.initF 1 0 2 1) []) ([] : List (Fin L1.g))⟩).stk
      (.b .out) =
  encodeCNF (InitFamily.initFam L1 1 0 [1, 2] [] 2 1 3)

end Cslib.Complexity.CookLevin.Tests
