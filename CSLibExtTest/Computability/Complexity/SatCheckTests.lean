/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.SatCheck
public meta import CSLibExt.Computability.Complexity.SatCheck

/-! Tests for the SAT verifier's clause-check driver, with stand-in lookups. -/

namespace Cslib.Complexity.SatVerifier.Check.Tests

open Turing MetaMathlibExt Cslib.Complexity.SatVerifier Cslib.Logic.PL

/-- Step a `TM2` program, with fuel, until the next step would halt; return the last
configuration with a label. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ
  | 0, c => c
  | n + 1, c => match TM2.step M c with
    | some c' => if c'.l.isSome then runF M n c' else c
    | none => c

/-- A stand-in lookup that answers `c` for every name. -/
private def constLk (c : Bool) : Unit → Stmt Unit :=
  fun _ => .push .V (fun _ => .bit c) (.goto fun _ => .inl .ret)

/-- Run the driver on `φ` with the stand-in lookup answering `c`; report the final label. -/
private def verdict (c : Bool) (φ : CNF) : Option (DLab ⊕ Unit) :=
  (runF (prog (constLk c) ()) 10000
    ⟨some (.inl .start), false, fun k => if k = .T then (toks φ).reverse else []⟩).l

-- Answer `true`: a clause passes iff it has a positive literal.
#guard verdict true [[(1, false)], [(2, true)]] = some (.inl .no)
#guard verdict true [[(1, false), (3, true)], [(2, true)]] = some (.inl .yes)
-- Answer `false`: a clause passes iff it has a negative literal.
#guard verdict false [[(1, false), (3, true)], [(2, true)]] = some (.inl .no)
#guard verdict false [[(1, false), (3, true)], [(0, false)]] = some (.inl .yes)
-- No clauses: accept. An empty clause: reject.
#guard verdict true [] = some (.inl .yes)
#guard verdict true [[(1, true)], []] = some (.inl .no)
-- Long names (`encodeNat 12 = [false, false, true, true]`) are dropped whole.
#guard verdict true [[(12, false), (5, true)], [(12, true)]] = some (.inl .yes)

-- The driver halts with the token stack consumed on acceptance.
#guard ((runF (prog (constLk true) ()) 10000 ⟨some (.inl .start), false,
    fun k => if k = .T then (toks [[(12, true)], [(1, true)]]).reverse else []⟩).stk .T).isEmpty

end Cslib.Complexity.SatVerifier.Check.Tests
