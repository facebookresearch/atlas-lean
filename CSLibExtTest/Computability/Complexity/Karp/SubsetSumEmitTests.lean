/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.SubsetSumEmit
public meta import CSLibExt.Computability.Complexity.Karp.SubsetSumEmit

/-! Tests for the VERTEX-COVER → SUBSET-SUM component machine and its bit-list lemmas. -/

namespace Cslib.Complexity.Karp.EmitSS.Tests

open Turing Cslib.Complexity.SatVerifier Computability

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

/-- Run `prog` on `x` from `start`. -/
private def go (x : List Bool) : TM2.Cfg Γ Lab Bool × ℕ :=
  runF prog 100000 0 ⟨some start, false, init x⟩

/-- The run halts at `done`, within the bound of `run`, with `reduceSS x` on `O`. -/
private def ok (x : List Bool) : Bool :=
  let (c, t) := go x
  c.l == some .done && t ≤ 40 * (x.length + 1) ^ 4 && (c.stk .O : List Bool) == reduceSS x

-- The triangle (`k = 2`, all three pairs edges) and the path `0 - 1 - 2` (`k = 1`).
#guard ok (encodeKG 2 3 [true, true, true])
#guard (go (encodeKG 2 3 [true, true, true])).1.stk .O = encodeSS [69, 84, 81, 1, 4, 16] 170
#guard ok (encodeKG 1 3 [false, true, true])
#guard (go (encodeKG 1 3 [false, true, true])).1.stk .O = encodeSS [68, 84, 80, 0, 4, 16] 104
-- `n = 0`, `n = 1`, `n = 2` (edge and no edge).
#guard ok (encodeKG 0 0 [])
#guard (go (encodeKG 0 0 [])).1.stk .O = encodeSS [] 0
#guard ok (encodeKG 1 0 [])
#guard ok (encodeKG 0 1 [])
#guard (go (encodeKG 1 1 [])).1.stk .O = encodeSS [1] 1
#guard ok (encodeKG 1 2 [true])
#guard (go (encodeKG 1 2 [true])).1.stk .O = encodeSS [5, 5, 1] 6
#guard ok (encodeKG 0 2 [false])
-- `k = 0` (the target keeps only edge digits; with no edges it is `0`) and `k > n`.
#guard ok (encodeKG 0 3 [true, false, true])
#guard ok (encodeKG 0 3 [false, false, false])
#guard (go (encodeKG 0 3 [false, false, false])).1.stk .O = encodeSS [64, 64, 64, 0, 0, 0] 0
#guard ok (encodeKG 5 3 [true, false, true])
-- A larger graph (`n = 5`, ten pair bits) and `n = 4` with one edge.
#guard ok (encodeKG 2 5 [true, false, false, true, true, false, true, false, false, true])
#guard ok (encodeKG 0 4 [false, false, false, false, false, true])
-- Sweep: every graph on 4 vertices with `k ≤ 4` (one bit of every pair pattern per `k`).
#guard (List.range 64).all fun g =>
  ok (encodeKG (g % 5) 4 ((List.range 6).map fun i => g / 2 ^ i % 2 == 1))
-- A wrong bit count: too few, too many.
#guard ok (encodeKG 2 3 [true, true])
#guard (go (encodeKG 2 3 [true, true])).1.stk .O = noSS
#guard ok (encodeKG 2 3 [true, true, true, false])
#guard (go (encodeKG 2 3 [true, true, true, false])).1.stk .O = noSS
#guard ok (encodeKG 0 0 [true])
-- Malformed: `X` ends inside `k` or inside `n`.
#guard ok []
#guard ok [true]
#guard ok [true, false, true]
#guard ok [false, true, true, true]
#guard (go [true, false, true]).1.stk .O = noSS

-- The bit-list lemmas on small cases.
#guard MetaMathlibExt.TM2Recursive.bitsVal [true, false, true] = 5
#guard encodeNat (MetaMathlibExt.TM2Recursive.bitsVal [true, true, false, false]) = [true, true]
#guard edgeOut [true, false, true] = (List.range 3).flatMap fun q =>
  MetaMathlibExt.BitstringEncoding.delimit (encodeNat (edgeNum [true, false, true] q))
#guard tri 5 = (pairs 5).length

end Cslib.Complexity.Karp.EmitSS.Tests
