/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.PathMachine
public meta import CSLibExt.Computability.Complexity.PathMachine

/-! Tests for the PATH marking machine: fuelled runs compared with `pathCheck`. -/

namespace Cslib.Complexity.Path.Machine.Tests

open Turing Cslib.Complexity.SatVerifier

/-- Step a `TM2` program, with fuel, until the next step would halt; return the last
configuration with a label and the number of steps taken. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ × ℕ
  | 0, t, c => (c, t)
  | n + 1, t, c => match TM2.step M c with
    | some c' => if c'.l.isSome then runF M n (t + 1) c' else (c, t)
    | none => (c, t)

/-- The initial stacks: `x` on `X` as input bits, every other stack empty. -/
private def init (x : List Bool) : ∀ k, List (Γ k)
  | .X => x.map Sym.bit
  | _ => []

/-- Run `prog` on `x` from `start`, with the fuel of `run`'s time bound. -/
private def go (x : List Bool) : TM2.Cfg Γ Lab Bool × ℕ :=
  runF prog (8 * (x.length + 1) ^ 4) 0 ⟨some start, false, init x⟩

/-- The run halts at `done` within `8 (|x| + 1)²` steps (inside `run`'s `8 (|x| + 1)⁴`), with
`[pathCheck x]` on `O`. -/
private def ok (x : List Bool) : Bool :=
  let (c, t) := go x
  c.l == some .done && t ≤ 8 * (x.length + 1) ^ 2 && (c.stk .O : List Bool) == [pathCheck x]

-- A chain listed backwards needs `n - 1` passes; `s = t`; targets out of range; ignored arcs.
#guard ok (encodeP 0 3 4 [(2, 3), (1, 2), (0, 1)])
#guard ((go (encodeP 0 3 4 [(2, 3), (1, 2), (0, 1)])).1.stk .O : List Bool) = [true]
#guard ((go (encodeP 0 3 4 [(2, 3), (1, 2)])).1.stk .O : List Bool) = [false]
#guard ok (encodeP 0 5 6 [(4, 5), (3, 4), (2, 3), (1, 2), (0, 1)])
#guard ok (encodeP 0 5 6 [(4, 5), (3, 4), (2, 3), (1, 2)])
#guard ok (encodeP 3 0 4 [(2, 3), (1, 2), (0, 1)])
#guard ok (encodeP 2 2 3 []) && ok (encodeP 3 3 3 [])
#guard ok (encodeP 0 1 1 [(0, 1)]) && ok (encodeP 0 2 2 [(0, 5), (5, 1)])
#guard ok (encodeP 0 1 2 [(0, 5), (0, 1)]) && ok (encodeP 5 1 2 [(5, 1)])
-- Malformed inputs: cut-off numbers, a dangling half-pair.
#guard ok [] && ok [true, false] && ok [false, false] && ok [false, false, true]
#guard ok (encodeP 0 1 2 [] ++ [true]) && ok (encodeP 0 1 2 [] ++ [false])
#guard ok (encodeP 0 1 2 [(0, 1)] ++ [true, false])
-- Every bit string of length at most 10.
#guard (List.range 11).all fun l => (List.range (2 ^ l)).all fun m =>
  ok ((List.range l).map fun i => m / 2 ^ i % 2 == 1)
-- Every digraph on 3 vertices without loops, every `s`, `t`, both edge orders.
#guard (List.range 64).all fun g =>
  let es := ([(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)].zip
    ((List.range 6).map fun i => g / 2 ^ i % 2 == 1)).filterMap fun p => if p.2 then p.1 else none
  (List.range 3).all fun s => (List.range 3).all fun t =>
    ok (encodeP s t 3 es) && ok (encodeP s t 3 es.reverse)

end Cslib.Complexity.Path.Machine.Tests
