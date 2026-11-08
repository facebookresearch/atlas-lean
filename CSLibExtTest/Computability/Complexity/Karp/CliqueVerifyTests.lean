/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.CliqueVerify
public meta import CSLibExt.Computability.Complexity.Karp.CliqueVerify

/-! Tests for the CLIQUE / INDEPENDENT-SET / VERTEX-COVER verifier: fuelled runs of the machine
against `kgCheck`. -/

namespace Cslib.Complexity.Karp.KGVerify.Tests

open Turing Cslib.Complexity.Karp Cslib.Complexity.SatVerifier

/-- Step a `TM2` program, with fuel, until the next step would halt; return the last
configuration with a label. -/
private def runF {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → TM2.Stmt Γ Λ σ) : ℕ → TM2.Cfg Γ Λ σ → TM2.Cfg Γ Λ σ
  | 0, c => c
  | n + 1, c => match TM2.step M c with
    | some c' => if c'.l.isSome then runF M n c' else c
    | none => c

/-- The final label of `prog m` on `x` and `w`, with the fuel of `run`'s time bound. -/
private def verdict (m : Mode) (x w : List Bool) : Option Lab :=
  (runF (prog m) (8 * (x.length + w.length + 1) ^ 3) ⟨some start, false,
    fun k => if k = .X then x.map Sym.bit else if k = .W then w.map Sym.bit else []⟩).l

/-- The machine's verdict is `kgCheck`'s, in every mode. -/
private def agrees (x w : List Bool) : Bool :=
  [Mode.clique, .indep, .cover].all fun m =>
    verdict m x w == some (if kgCheck m x w then .yes else .no)

/-- The triangle on `{0, 1, 2}`: pairs `(0, 2), (0, 1), (1, 2)`. -/
private def tri (k : ℕ) : List Bool := encodeKG k 3 [true, true, true]

/-- The path `0 - 1 - 2`: only `(0, 2)` is missing. -/
private def path (k : ℕ) : List Bool := encodeKG k 3 [false, true, true]

/-- Three vertices, no edges. -/
private def none3 (k : ℕ) : List Bool := encodeKG k 3 [false, false, false]

-- Triangle: every pair is an edge, so any `k` vertices form a clique.
#guard kgCheck .clique (tri 3) [true, true, true] && kgCheck .clique (tri 2) [true, false, true]
#guard !kgCheck .indep (tri 2) [true, false, true] && kgCheck .indep (tri 1) [false, true, false]
#guard kgCheck .cover (tri 2) [false, true, true] && !kgCheck .cover (tri 1) [false, true, false]
#guard agrees (tri 3) [true, true, true] && agrees (tri 2) [true, false, true]
#guard agrees (tri 1) [false, true, false] && agrees (tri 2) [false, true, true]

-- Path: `{0, 1}` is a clique but not independent, `{0, 2}` the reverse; `{1}` covers it.
#guard kgCheck .clique (path 2) [true, true, false] && !kgCheck .clique (path 2) [true, false, true]
#guard kgCheck .indep (path 2) [true, false, true] && !kgCheck .indep (path 2) [true, true, false]
#guard kgCheck .cover (path 1) [false, true, false] && !kgCheck .cover (path 1) [true, false, false]
#guard agrees (path 2) [true, true, false] && agrees (path 2) [true, false, true]
#guard agrees (path 1) [false, true, false] && agrees (path 1) [true, false, false]
#guard agrees (path 2) [false, true, true] && agrees (path 3) [true, true, true]

-- The empty graph `n = 0`: only `k = 0` is a yes-instance.
#guard kgCheck .clique (encodeKG 0 0 []) [] && kgCheck .cover (encodeKG 0 0 []) []
#guard !kgCheck .indep (encodeKG 1 0 []) [true]
#guard agrees (encodeKG 0 0 []) [] && agrees (encodeKG 0 0 []) [true, false]
#guard agrees (encodeKG 1 0 []) [] && agrees (encodeKG 1 0 []) [true]

-- `k = 0`: the empty set is a clique and an independent set, and covers only edgeless graphs.
#guard kgCheck .clique (tri 0) [false, false, false]
#guard !kgCheck .cover (tri 0) [false, false, false]
#guard kgCheck .cover (none3 0) [false, false, false]
#guard agrees (tri 0) [false, false, false] && agrees (none3 0) [false, false, false]

-- Wrong `k`: the number of chosen vertices must be exactly `k`.
#guard !kgCheck .clique (tri 3) [true, true, false] && !kgCheck .clique (tri 1) [true, true, false]
#guard agrees (tri 3) [true, true, false] && agrees (tri 1) [true, true, false]
#guard agrees (none3 1) [true, true, true] && agrees (none3 2) [true, true, false]

-- Short witness (`n > |w|`) rejects; bits past the first `n` are ignored.
#guard !kgCheck .clique (tri 2) [true, true] && kgCheck .clique (tri 2) [true, true, false, true]
#guard agrees (tri 2) [true, true] && agrees (tri 0) [] && agrees (tri 2) [true, true, false, true]

-- Malformed instances: an unterminated `k` or `n`.
#guard agrees [] [] && agrees [true, true] [] && agrees [false] [] && agrees [true, false, true] []
#guard !kgCheck .clique [false] [] && !kgCheck .cover [true, false, true] [true]

-- The bit count must be exactly `(pairs n).length`: an extra trailing bit or a missing bit
-- rejects.
#guard !kgCheck .clique (encodeKG 2 3 [true, true, true, true]) [true, true, false]
#guard !kgCheck .clique (encodeKG 2 3 [true, true]) [true, true, false]
#guard agrees (encodeKG 2 3 [true, true, true, true]) [true, true, false]
#guard agrees (encodeKG 2 3 [true, true]) [true, true, false]
#guard agrees (encodeKG 0 0 [true]) [] && agrees (encodeKG 0 1 [true]) [false]

-- A 4-vertex graph with edges `{0, 1}, {1, 2}, {2, 3}, {1, 3}` (pairs `(0,3), (0,2), (0,1),
-- (1,3), (1,2), (2,3)`): `{1, 2, 3}` is a triangle, `{0, 2}` independent, `{1, 2}` a cover.
#guard kgCheck .clique (encodeKG 3 4 [false, false, true, true, true, true])
  [false, true, true, true]
#guard kgCheck .indep (encodeKG 2 4 [false, false, true, true, true, true])
  [true, false, true, false]
#guard kgCheck .cover (encodeKG 2 4 [false, false, true, true, true, true])
  [false, true, true, false]
#guard [[false, true, true, true], [true, false, true, false], [false, true, true, false],
  [true, true, false, false], [true, true, true, true]].all fun w =>
    (List.range 5).all fun k => agrees (encodeKG k 4 [false, false, true, true, true, true]) w

-- Exhaustively on all graphs and witnesses with `n = 3` and `k ≤ 3`.
#guard (List.range 8).all fun g => (List.range 8).all fun s => (List.range 4).all fun k =>
  agrees (encodeKG k 3 [g % 2 == 1, g / 2 % 2 == 1, g / 4 % 2 == 1])
    [s % 2 == 1, s / 2 % 2 == 1, s / 4 % 2 == 1]

-- `prog m` halts at `yes`/`no` with a halting statement.
#guard (prog .clique .yes matches .halt) && (prog .cover .no matches .halt)

end Cslib.Complexity.Karp.KGVerify.Tests
