/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.ColorVerify
public meta import CSLibExt.Computability.Complexity.Karp.ColorVerify

/-! Tests for the 3-COLOR verifier: the parser, and fuelled runs of the machine against
`colCheck`. -/

namespace Cslib.Complexity.Karp.ColVerify.Tests

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
  (runF prog (8 * (x.length + w.length + 1) ^ 3) ⟨some start, false,
    fun k => if k = .X then x.map Sym.bit else if k = .W then w.map Sym.bit else []⟩).l

/-- The machine's verdict is `colCheck`'s. -/
private def agrees (x w : List Bool) : Bool :=
  verdict x w == some (if colCheck x w then .yes else .no)

/-- The witness of a list of colors: `0 ↦ 00`, `1 ↦ 01`, `2 ↦ 10`. -/
private def wit (cs : List ℕ) : List Bool := cs.flatMap fun c => [c == 2, c == 1]

/-- The `k` low bits of `m`, least significant first. -/
private def bits (k m : ℕ) : List Bool := (List.range k).map fun i => m / 2 ^ i % 2 == 1

-- The parser inverts `encodeE`, and fails on a missing or cut-off number or a half pair.
#guard Karp.decodeE (encodeE 3 [(0, 2), (1, 1)]) = some (3, [(0, 2), (1, 1)])
#guard Karp.decodeE (encodeE 0 []) = some (0, []) &&
  Karp.decodeE (encodeE 2 [(5, 0)]) = some (2, [(5, 0)])
#guard Karp.decodeE [] = none && Karp.decodeE [true, true] = none
#guard Karp.decodeE (encodeE 2 [] ++ [true, false]) = none
#guard Karp.decodeE (encodeE 2 [] ++ [false, true]) = none &&
  Karp.decodeE (encodeE 2 [] ++ [true]) = none

/-- The triangle on `{0, 1, 2}`. -/
private def tri : List Bool := encodeE 3 [(0, 1), (1, 2), (0, 2)]

-- Triangle: a proper coloring passes, an improper one fails; every coloring, with the machine.
#guard colCheck tri (wit [0, 1, 2]) && agrees tri (wit [0, 1, 2])
#guard !colCheck tri (wit [0, 1, 1]) && agrees tri (wit [0, 1, 1])
#guard (List.range 27).all fun m =>
  let cs := [m % 3, m / 3 % 3, m / 9 % 3]
  colCheck tri (wit cs) == cs.Nodup && agrees tri (wit cs)

-- `K4` (`noCol`) has no 3-coloring: every witness of at most `8` bits fails.
#guard (List.range 9).all fun l => (List.range (2 ^ l)).all fun m =>
  !colCheck noCol (bits l m) && agrees noCol (bits l m)

-- Loops are ignored, as long as their vertex exists.
#guard colCheck (encodeE 1 [(0, 0)]) (wit [1]) && agrees (encodeE 1 [(0, 0)]) (wit [1])
#guard colCheck (encodeE 2 [(1, 1), (0, 1)]) (wit [2, 0])
#guard agrees (encodeE 2 [(1, 1), (0, 1)]) (wit [2, 0])
#guard !colCheck (encodeE 2 [(2, 2)]) (wit [0, 1]) && agrees (encodeE 2 [(2, 2)]) (wit [0, 1])

-- Out-of-range endpoints reject, on either side, even with a proper coloring of the rest.
#guard !colCheck (encodeE 3 [(0, 3)]) (wit [0, 1, 2]) && agrees (encodeE 3 [(0, 3)]) (wit [0, 1, 2])
#guard !colCheck (encodeE 3 [(3, 0)]) (wit [0, 1, 2]) && agrees (encodeE 3 [(3, 0)]) (wit [0, 1, 2])
#guard agrees (encodeE 3 [(0, 1), (5, 1)]) (wit [0, 1, 2] ++ wit [0, 0, 0])
#guard agrees (encodeE 0 [(0, 0)]) [] && agrees (encodeE 0 []) []

-- A `11` code rejects, also on a vertex no edge touches; past the first `2 n` bits it is ignored.
#guard !colCheck (encodeE 3 [(0, 2)]) [false, false, true, true, true, false]
#guard agrees (encodeE 3 [(0, 2)]) [false, false, true, true, true, false]
#guard colCheck (encodeE 2 [(0, 1)]) (wit [0, 1] ++ [true, true])
#guard agrees (encodeE 2 [(0, 1)]) (wit [0, 1] ++ [true, true])

-- A short witness rejects.
#guard !colCheck (encodeE 3 [(0, 1)]) (wit [0, 1]) && agrees (encodeE 3 [(0, 1)]) (wit [0, 1])
#guard agrees (encodeE 3 [(0, 1)]) (wit [0, 1] ++ [true]) && agrees (encodeE 1 []) []

-- Malformed instances reject.
#guard agrees [] [] && agrees [true] [] && agrees (encodeE 2 [] ++ [true, false]) (wit [0, 1])
#guard agrees (encodeE 2 [] ++ [false, true, true]) (wit [0, 1])
#guard !colCheck (encodeE 2 [(0, 1)] ++ [false]) (wit [0, 1])
#guard agrees (encodeE 2 [(0, 1)] ++ [false]) (wit [0, 1])

-- Exhaustively: all subsets of five edges on three vertices (a loop and a repeat among them),
-- with all witnesses of six bits.
#guard (List.range 32).all fun g => (List.range 64).all fun m =>
  agrees (encodeE 3 ([(0, 1), (1, 2), (0, 2), (1, 1), (2, 0)].zip (bits 5 g)
    |>.filterMap fun p => if p.2 then some p.1 else none)) (bits 6 m)

-- `prog` halts at `yes` and `no` with a halting statement.
#guard (prog .yes matches .halt) && (prog .no matches .halt)

end Cslib.Complexity.Karp.ColVerify.Tests
