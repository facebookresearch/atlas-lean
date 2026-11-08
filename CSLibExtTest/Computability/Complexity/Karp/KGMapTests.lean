/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.KGMap
public meta import CSLibExt.Computability.Complexity.Karp.KGMap

/-! Tests for the CLIQUE → INDEPENDENT-SET / INDEPENDENT-SET → VERTEX-COVER component machine. -/

namespace Cslib.Complexity.Karp.KGMap.Tests

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

/-- Run `prog m` on `x` from `start`. -/
private def go (m : Mode) (x : List Bool) : TM2.Cfg Γ Lab Bool × ℕ :=
  runF (prog m) 10000 0 ⟨some start, false, init x⟩

/-- The run halts at `done`, within `3 · (|x| + 1)` steps, with `m.f x` on `O`. -/
private def ok (m : Mode) (x : List Bool) : Bool :=
  let (c, t) := go m x
  c.l == some .done && t ≤ 3 * (x.length + 1) && (c.stk .O : List Bool) == m.f x

/-- Both modes pass `ok` on `x`. -/
private def okBoth (x : List Bool) : Bool := ok .flip x && ok .vc x

-- A valid instance with `k < n`.
#guard okBoth (encodeKG 2 3 [false, false, true])
#guard (go .flip (encodeKG 2 3 [false, false, true])).1.stk .O = encodeKG 2 3 [true, true, false]
#guard (go .vc (encodeKG 2 3 [false, false, true])).1.stk .O = encodeKG 1 3 [false, false, true]
-- `n = 0`: `k = 0`, and `k = 1 > n` (`vc` gives `noKG`).
#guard okBoth (encodeKG 0 0 [])
#guard okBoth (encodeKG 1 0 [])
#guard (go .vc (encodeKG 1 0 [])).1.stk .O = noKG
-- `k = 0`.
#guard okBoth (encodeKG 0 3 [true, false, true])
#guard (go .vc (encodeKG 0 3 [true, false, true])).1.stk .O = encodeKG 3 3 [true, false, true]
-- `k = n`.
#guard okBoth (encodeKG 3 3 [true, true, false])
#guard (go .vc (encodeKG 3 3 [true, true, false])).1.stk .O = encodeKG 0 3 [true, true, false]
-- `k > n`.
#guard okBoth (encodeKG 4 3 [false, false, true])
#guard (go .vc (encodeKG 4 3 [false, false, true])).1.stk .O = noKG
#guard (go .flip (encodeKG 4 3 [false, false, true])).1.stk .O = encodeKG 4 3 [true, true, false]
-- A larger graph (`n = 5`, ten pair bits).
#guard okBoth (encodeKG 2 5 [true, false, false, true, true, false, true, false, false, true])
-- Malformed: `X` ends inside `k` or inside `n`.
#guard okBoth []
#guard okBoth [true]
#guard okBoth [true, false, true]
#guard okBoth [false, true, true]
#guard (go .flip [true, false, true]).1.stk .O = noKG
#guard (go .vc []).1.stk .O = noKG

end Cslib.Complexity.Karp.KGMap.Tests
