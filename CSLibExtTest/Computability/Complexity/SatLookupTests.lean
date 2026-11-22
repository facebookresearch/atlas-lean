/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.SatLookup
public meta import CSLibExt.Computability.Complexity.SatLookup

/-! Tests for the lookup machine of the SAT verifier. -/

namespace Cslib.Complexity.SatVerifier.Lookup.Tests

open Turing Computability Cslib.Complexity.SatVerifier Cslib.Complexity.SatVerifier.Lookup

/-- Step a `TM2` program until it halts, with fuel. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ
  | 0, c => c
  | n + 1, c => match TM2.step M c with
    | some c' => runF M n c'
    | none => c

/-- The start configuration: query `q` above the rest `R` on `T`, table `es` on `B`. -/
private def cfg₀ (q : List Bool) (R : List Sym) (es : List Ent) :
    TM2.Cfg (fun _ : K => Sym) Lab Bool :=
  ⟨some start, false, stk ((q.map Sym.bit).reverse ++ R) (tblStk es) [] [] [] []⟩

/-- Run to the halt and report the six stacks `T, B, S, A, C, V`. -/
private def finStks (q : List Bool) (R : List Sym) (es : List Ent) : List (List Sym) :=
  let c := runF prog 100000 (cfg₀ q R es)
  [c.stk .T, c.stk .B, c.stk .S, c.stk .A, c.stk .C, c.stk .V]

/-- The expected final stacks: `T`, `B` as they started, `bit (liveVal es q)` on `V`. -/
private def expStks (q : List Bool) (R : List Sym) (es : List Ent) : List (List Sym) :=
  [(q.map Sym.bit).reverse ++ R, tblStk es, [], [], [], [Sym.bit (liveVal es q)]]

/-- Names `1` (twice, first `true` then `false`), `2` (dead, then live `true`), `0` (the empty
name, `true`) and `3` (`false`). -/
private def es₁ : List Ent :=
  [(encodeNat 1, some true), (encodeNat 2, none), (encodeNat 1, some false),
    (encodeNat 2, some true), (encodeNat 0, some true), (encodeNat 3, some false)]

/-- A rest below the query block that starts with a marker. -/
private def R₁ : List Sym := [.lit true, .bit false, .cl]

#guard encodeNat 0 = [] ∧ encodeNat 3 = [true, true] ∧ encodeNat 7 = [true, true, true]

-- Repeated name: the first occurrence wins (`true`, not the later `false`).
#guard finStks (encodeNat 1) R₁ es₁ = expStks (encodeNat 1) R₁ es₁
#guard (finStks (encodeNat 1) R₁ es₁).getLast? = some [.bit true]
-- A dead entry is skipped: name `2` gets `true` from its later live entry.
#guard finStks (encodeNat 2) [] es₁ = expStks (encodeNat 2) [] es₁
#guard (finStks (encodeNat 2) [] es₁).getLast? = some [.bit true]
-- The empty name matches only the empty name.
#guard finStks (encodeNat 0) R₁ es₁ = expStks (encodeNat 0) R₁ es₁
#guard (finStks (encodeNat 0) R₁ es₁).getLast? = some [.bit true]
-- Name `3` is live `false`.
#guard (finStks (encodeNat 3) R₁ es₁).getLast? = some [.bit false]
-- Absent names (`7` extends the table name `3`; `5`) get the default `false`.
#guard finStks (encodeNat 7) R₁ es₁ = expStks (encodeNat 7) R₁ es₁
#guard (finStks (encodeNat 7) R₁ es₁).getLast? = some [.bit false]
#guard (finStks (encodeNat 5) [] es₁).getLast? = some [.bit false]
-- First occurrence `false` beats a later `true`; a name whose only entry is dead reads `false`.
#guard (finStks (encodeNat 1) [] [(encodeNat 1, some false), (encodeNat 1, some true)]).getLast? =
  some [.bit false]
#guard (finStks (encodeNat 4) [] [(encodeNat 4, none)]).getLast? = some [.bit false]
-- The empty table.
#guard finStks (encodeNat 1) R₁ [] = expStks (encodeNat 1) R₁ []

-- The run reaches `done` within the bound `8 · |tblStk es| + 4` (and halts one step later).
#guard ([0, 1, 2, 3, 5, 7].map encodeNat).all fun q =>
  ((runF prog (8 * (tblStk es₁).length + 4) (cfg₀ q R₁ es₁)).l).all (· == Lab.done)
#guard (runF prog 100000 (cfg₀ (encodeNat 1) R₁ es₁)).l = none

end Cslib.Complexity.SatVerifier.Lookup.Tests
