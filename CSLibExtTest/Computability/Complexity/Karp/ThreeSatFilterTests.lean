/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ThreeSatFilter
public meta import CSLibExt.Computability.Complexity.Karp.ThreeSatFilter

/-! Tests for the clause-length filter. -/

namespace Cslib.Complexity.Karp.Filter3.Tests

open Turing Cslib.Logic.PL Cslib.Complexity.SatVerifier

/-- Step until halting or out of fuel. -/
private def runF (cap : Bool) : ℕ → TM2.Cfg (fun _ : K => Sym) Lab Bool →
    TM2.Cfg (fun _ : K => Sym) Lab Bool
  | 0, c => c
  | n + 1, c => match c.l with
    | some .pass | some .fail | none => c
    | _ => match TM2.step (prog cap) c with
      | some c' => runF cap n c'
      | none => c

/-- Final label and stacks from `start` on the token stack of `φ`, with the proved fuel. -/
private def final (cap : Bool) (φ : CNF) : TM2.Cfg (fun _ : K => Sym) Lab Bool :=
  runF cap (2 * (toks φ).length + 2) ⟨some start, false, st (toks φ).reverse []⟩

private def ok (cap : Bool) (φ : CNF) : Bool :=
  (final cap φ).l == some .pass && (final cap φ).stk .T == (toks φ).reverse &&
    (final cap φ).stk .U == []

private def bad (cap : Bool) (φ : CNF) : Bool := (final cap φ).l == some .fail

private def long : CNF := [[(1, true)], [(0, false), (2, true), (3, false), (5, true)], []]

-- Formulas with clauses of length at most three pass and keep their token stack.
#guard ok true []
#guard ok true [[]]
#guard ok true [[(1, true), (2, false), (3, true)], [(0, false)], [(6, true), (6, false)]]
-- A clause of length four fails, wherever it sits.
#guard bad true long
#guard bad true [[(1, true), (2, true), (3, true), (4, true)]]
#guard bad true [[(1, true), (2, true), (3, true), (4, true)], [(7, false)]]
-- Uncapped, everything passes.
#guard ok false long
#guard ok false [[(1, true), (2, true), (3, true), (4, true), (5, true), (6, true)]]

end Cslib.Complexity.Karp.Filter3.Tests
