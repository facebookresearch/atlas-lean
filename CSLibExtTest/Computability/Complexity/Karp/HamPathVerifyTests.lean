/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.HamPathVerify
public meta import CSLibExt.Computability.Complexity.Karp.HamPathVerify

/-! Tests for the HAMPATH verifier: the witness codec, `hamCheck` against brute force, and
fuelled runs of the machine against `hamCheck`. -/

namespace Cslib.Complexity.Karp.HamVerify.Tests

open Turing Cslib.Complexity.Karp Cslib.Complexity.SatVerifier

/-- Step a `TM2` program, with fuel, until the next step would halt; return the last
configuration with a label. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ
  | 0, c => c
  | n + 1, c => match TM2.step M c with
    | some c' => if c'.l.isSome then runF M n c' else c
    | none => c

/-- The final label of `prog` on `x` and `w`, with the fuel of `run`'s time bound. -/
private def verdict (x w : List Bool) : Option Lab :=
  (runF prog (100 * (x.length + w.length + 1) ^ 4) ⟨some start, false,
    fun k => if k = .X then x.map Sym.bit else if k = .W then w.map Sym.bit else []⟩).l

/-- The machine's verdict is `hamCheck`'s. -/
private def agrees (x w : List Bool) : Bool :=
  verdict x w == some (if hamCheck x w then .yes else .no)

/-- Brute force, independent of `hamOk`: `p` is a permutation of `0, …, n - 1` from `s` to `t`
whose consecutive pairs are listed. -/
private def isHamB (n : ℕ) (es : List (ℕ × ℕ)) (s t : ℕ) (p : List ℕ) : Bool :=
  (List.range n).permutations.contains p && p.head? == some s && p.getLast? == some t &&
    (p.zip p.tail).all es.contains

/-- All lists of length at most `l` over `0, …, m - 1`. -/
private def lists (m : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | l + 1 => [] :: (List.range m).flatMap fun v => (lists m l).map (v :: ·)

/-- The edge subsets of `cands` picked by the bits of `g`. -/
private def pick (cands : List (ℕ × ℕ)) (g : ℕ) : List (ℕ × ℕ) :=
  (cands.zip (List.range cands.length)).filterMap fun p =>
    if g / 2 ^ p.2 % 2 == 1 then some p.1 else none

-- The witness codec: round trips, and failures on a cut-off number.
#guard decodeW (encW [0, 3, 1]) = some [0, 3, 1] && decodeW (encW []) = some []
#guard encW [2, 0] = [true, true, false, false]
#guard decodeW [true] = none && decodeW (encW [1] ++ [true, true]) = none
#guard (lists 3 3).all fun p => decodeW (encW p) == some p

/-- The directed path `0 → 1 → 2`. -/
private def path3 : List Bool := Path.encodeP 0 2 3 [(0, 1), (1, 2)]

-- A valid path; the machine agrees.
#guard hamCheck path3 (encW [0, 1, 2]) && agrees path3 (encW [0, 1, 2])
-- A repeated vertex, every other condition met (loop `(1, 1)`, `t = 1`).
#guard !hamCheck (Path.encodeP 0 1 3 [(0, 1), (1, 1)]) (encW [0, 1, 1])
#guard agrees (Path.encodeP 0 1 3 [(0, 1), (1, 1)]) (encW [0, 1, 1])
-- A missing vertex.
#guard !hamCheck (Path.encodeP 0 2 3 [(0, 2)]) (encW [0, 2])
#guard agrees (Path.encodeP 0 2 3 [(0, 2)]) (encW [0, 2])
-- Wrong endpoints.
#guard !hamCheck (Path.encodeP 0 1 3 [(0, 1), (1, 2)]) (encW [0, 1, 2])
#guard agrees (Path.encodeP 0 1 3 [(0, 1), (1, 2)]) (encW [0, 1, 2])
#guard !hamCheck (Path.encodeP 1 2 3 [(0, 1), (1, 2)]) (encW [0, 1, 2])
#guard agrees (Path.encodeP 1 2 3 [(0, 1), (1, 2)]) (encW [0, 1, 2])
-- A step that is not an arc, and an arc listed the other way round.
#guard !hamCheck path3 (encW [0, 2, 1]) && agrees path3 (encW [0, 2, 1])
#guard !hamCheck (Path.encodeP 0 1 2 [(1, 0)]) (encW [0, 1])
#guard agrees (Path.encodeP 0 1 2 [(1, 0)]) (encW [0, 1])
-- An out-of-range vertex, every other condition met (listed edge `(0, 5)`, `t = 5`).
#guard !hamCheck (Path.encodeP 0 5 2 [(0, 5)]) (encW [0, 5])
#guard agrees (Path.encodeP 0 5 2 [(0, 5)]) (encW [0, 5])
-- One vertex; no vertices (rejected even with `n = 0`).
#guard hamCheck (Path.encodeP 0 0 1 []) (encW [0]) && agrees (Path.encodeP 0 0 1 []) (encW [0])
#guard !hamCheck (Path.encodeP 0 0 0 []) [] && agrees (Path.encodeP 0 0 0 []) []
-- Malformed instances: cut off before `s`, `t` or `n`, or a dangling half edge.
#guard agrees [] [] && agrees [true] (encW [0]) && agrees [false, true] (encW [0])
#guard agrees [false, false, true] (encW [0])
#guard !hamCheck (path3 ++ [true, false]) (encW [0, 1, 2])
#guard agrees (path3 ++ [true, false]) (encW [0, 1, 2])
#guard agrees (path3 ++ [true]) (encW [0, 1, 2])
-- Malformed witnesses: a cut-off number after a valid path, or alone.
#guard !hamCheck path3 (encW [0, 1, 2] ++ [true]) && agrees path3 (encW [0, 1, 2] ++ [true])
#guard agrees path3 [true] && agrees path3 [true, false, true]

/-- Candidate edges on three vertices, with a loop and both directions of one pair. -/
private def cands : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0), (1, 0), (2, 2)]

-- `hamCheck` against brute force: every graph on candidate edges, every `s, t < 3`, every
-- vertex list of length at most 3 over `0, …, 3`.
#guard (List.range 32).all fun g => (List.range 9).all fun st =>
  let es := pick cands g
  let x := Path.encodeP (st / 3) (st % 3) 3 es
  (lists 4 3).all fun p => hamCheck x (encW p) == isHamB 3 es (st / 3) (st % 3) p

-- `hamPathDec` against brute force on the same graphs: some permutation passes `hamCheck` iff
-- some permutation is a Hamiltonian path.
#guard (List.range 32).all fun g => (List.range 9).all fun st =>
  let es := pick cands g
  let x := Path.encodeP (st / 3) (st % 3) 3 es
  (List.range 3).permutations.any (fun p => hamCheck x (encW p)) ==
    (List.range 3).permutations.any (isHamB 3 es (st / 3) (st % 3))

-- The machine against `hamCheck`: every graph on candidate edges, `s = 0`, `t = 2`, every
-- vertex list of length at most 3 over `0, …, 3`.
#guard (List.range 32).all fun g =>
  (lists 4 3).all fun p => agrees (Path.encodeP 0 2 3 (pick cands g)) (encW p)

-- `prog` halts at `yes` and `no` with a halting statement.
#guard (prog .yes matches .halt) && (prog .no matches .halt)

end Cslib.Complexity.Karp.HamVerify.Tests
