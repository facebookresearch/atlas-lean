/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.SubsetSumVerify
public meta import CSLibExt.Computability.Complexity.Karp.SubsetSumVerify

/-! Tests for the SUBSET-SUM verifier: the parser, `ssCheck` against brute force, and fuelled
runs of the machine against `ssCheck`. -/

namespace Cslib.Complexity.Karp.SSVerify.Tests

open Turing Computability MetaMathlibExt.BitstringEncoding Cslib.Complexity.Karp
open Cslib.Complexity.SatVerifier

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
  (runF prog (16 * (x.length + w.length + 1) ^ 3) ⟨some start, false,
    fun k => if k = .X then x.map Sym.bit else if k = .W then w.map Sym.bit else []⟩).l

/-- The machine's verdict is `ssCheck`'s. -/
private def agrees (x w : List Bool) : Bool :=
  verdict x w == some (if ssCheck x w then .yes else .no)

/-- Every mask of length `n`. -/
private def masks : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (masks n).flatMap fun m => [false :: m, true :: m]

/-- The machine agrees with `ssCheck` on every mask as long as the instance. -/
private def agreesAll (as : List ℕ) (t : ℕ) : Bool :=
  (masks as.length).all fun w => agrees (encodeSS as t) w

/-- Brute force: does some sublist of `as` sum to `t`? -/
private def hits (as : List ℕ) (t : ℕ) : Bool := as.sublists.any fun l => l.sum == t

/-- `ssCheck` with some mask of length `|as|` is the brute-force answer. -/
private def checkMatches (as : List ℕ) (t : ℕ) : Bool :=
  (masks as.length).any (ssCheck (encodeSS as t)) == hits as t

-- The parser inverts the encoding, including zeros (`encodeNat 0 = []`) and no numbers.
#guard decodeSS (encodeSS [3, 5, 6] 11) = some ([3, 5, 6], 11)
#guard decodeSS (encodeSS [0, 2, 0] 0) = some ([0, 2, 0], 0)
#guard decodeSS (encodeSS [] 7) = some ([], 7)
#guard decodeSS (encodeSS [255, 1] 256) = some ([255, 1], 256)
-- Non-canonical blocks (non-empty, ending in `false`) and malformed inputs do not parse.
#guard decodeSS (delimit [false] ++ delimit [true]) = none
#guard decodeSS (delimit [true] ++ delimit [true, false]) = none
#guard decodeSS [] = none && decodeSS [true] = none && decodeSS [true, true] = none
#guard decodeSS (delimit [true] ++ [true]) = none
#guard decodeSS (delimit [true] ++ [true, false, true]) = none

-- `ssCheck` with masks matches a brute-force sublist search.
#guard (List.range 16).all fun t => checkMatches [3, 5, 6] t
#guard (List.range 6).all fun t => checkMatches [0, 2, 0, 3] t
#guard checkMatches [] 0 && checkMatches [] 1 && checkMatches [7, 1] 8

-- Masks choose by position; missing bits are `false`, extra bits are ignored.
#guard ssCheck (encodeSS [3, 5, 6] 11) [false, true, true]
#guard !ssCheck (encodeSS [3, 5, 6] 11) [true, true, false]
#guard ssCheck (encodeSS [3, 5, 6] 3) [true]
#guard ssCheck (encodeSS [3, 5, 6] 0) []
#guard ssCheck (encodeSS [3, 5, 6] 9) [true, false, true, true, true]

-- The machine: every mask on small instances, including `t = 0` and no numbers.
#guard agreesAll [3, 5, 6] 11 && agreesAll [3, 5, 6] 9 && agreesAll [3, 5, 6] 14
#guard agreesAll [3, 5, 6] 0 && agreesAll [3, 5, 6] 4 && agreesAll [3, 5, 6] 15
#guard agreesAll [] 0 && agreesAll [] 1
-- Zero numbers (empty blocks) anywhere, and target `0`.
#guard agreesAll [0, 2, 0] 2 && agreesAll [0, 2, 0] 0 && agreesAll [0] 0 && agreesAll [0] 1
-- Carries across several positions, and sums longer than every number.
#guard agreesAll [7, 1] 8 && agreesAll [15, 17] 32 && agreesAll [255, 1] 256
#guard agreesAll [1, 1, 1, 1] 4 && agreesAll [1, 1, 1, 1] 3 && agreesAll [6, 3, 5] 14
#guard agreesAll [255, 1] 255 && agreesAll [255, 1] 0
#guard ssCheck (encodeSS [255, 1] 256) [true, true] && agrees (encodeSS [255, 1] 256) [true, true]

-- Short and long masks.
#guard agrees (encodeSS [3, 5, 6] 3) [true] && agrees (encodeSS [3, 5, 6] 0) []
#guard agrees (encodeSS [3, 5, 6] 8) [true, true] && agrees (encodeSS [3, 5, 6] 5) [false, true]
#guard agrees (encodeSS [3, 5, 6] 9) [true, false, true, true, true]

-- Non-canonical blocks: in the target, in a chosen number, in a skipped number.
#guard agrees (delimit [false] ++ delimit [true]) [true]
#guard agrees (delimit [true, false] ++ delimit [true]) [true]
#guard agrees (delimit [true] ++ delimit [true, false]) [true]
#guard agrees (delimit [true] ++ delimit [true, false]) [false]
#guard agrees (delimit [true] ++ delimit [true] ++ delimit [false]) [true, true]

-- Malformed inputs: empty, a lone `true`, an unterminated target or number, a dangling bit.
#guard agrees [] [] && agrees [true] [] && agrees [true, true] [true]
#guard agrees [true, false, true] [] && agrees (delimit [true] ++ [true]) [true]
#guard agrees (delimit [true] ++ [true, true, true]) [true]
#guard agrees (delimit [true] ++ [true]) [false]
#guard agrees (delimit [true] ++ [true, true, true]) [false]

end Cslib.Complexity.Karp.SSVerify.Tests
