/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.CooperEmitSpec
public meta import CSLibExt.Computability.Complexity.Karp.CooperEmitSpec

/-! Tests for the emission of Cooper's network from the SAT token stack. -/

namespace Cslib.Complexity.Karp.EmitCooper.Tests

open Cslib.CookLevin Cslib.Logic.LegacyPL Cslib.Complexity.SatVerifier Cslib.Complexity.Cooper

/-- **The emission writes Cooper's network on `φ`**: on the token stack of `φ`, the emission is
the code of `cooperNet φ`. -/
abbrev EmitsNet (φ : CNF) : Prop :=
  emitTok (toks φ).reverse = encodeRatNet (cooperNet φ)

/-! ### Fixed formulas -/

/-- The empty formula: the constant-true node alone. -/
example : EmitsNet [] := by
  decide +kernel

/-- One empty clause: its constant-false node, closed by an AND node. -/
example : EmitsNet [[]] := by
  decide +kernel

/-- Variable `0`, whose name is the empty bit string. -/
example : EmitsNet [[(0, true)]] := by
  decide +kernel

/-- Cooper's example `3SAT_ex`. -/
example : EmitsNet cooperEx := by
  decide +kernel

/-- The unsatisfiable control. -/
example : EmitsNet cooperUnsat := by
  decide +kernel

/-- A variable and its negation in one clause: one root, two OR nodes. -/
example : EmitsNet [[(1, true), (1, false)]] := by
  decide +kernel

/-- Four clauses, one of them empty, with the variables `0` and `5` repeated across clauses. -/
example : EmitsNet [[(0, true), (3, false)], [], [(0, false), (5, true)],
    [(5, false), (0, true), (2, true)]] := by
  decide +kernel

/-! ### Random formulas

Up to four clauses of up to four literals over the variables `0` to `5`. -/

example : EmitsNet [[(4, false), (5, false)], []] := by
  decide +kernel

example : EmitsNet [[(4, false), (4, false), (5, false), (3, false)],
    [(3, true), (4, true), (2, false), (3, true)]] := by
  decide +kernel

example : EmitsNet [[(5, true), (3, true), (2, false)],
    [(5, true), (2, true), (4, true), (3, true)], [(2, true), (5, true), (3, true), (3, false)],
    [(3, false), (3, false), (4, false), (3, false)]] := by
  decide +kernel

/-! ### Cooper's example in detail -/

/-- Cooper's example has 20 nodes. -/
example : (walkTok (toks cooperEx).reverse).n = 20 := by
  decide +kernel

/-- The dictionary after Cooper's example, latest entry first: the variables `1`, `2`, `3`, `4`
under their names, least significant bit first, with the roots `12`, `6`, `4`, `2`. -/
example : (walkTok (toks cooperEx).reverse).dict =
    [([true], 12), ([false, true], 6), ([true, true], 4), ([false, false, true], 2)] := by
  decide +kernel

/-- The code of Cooper's example has 823 bits. -/
example : (emitTok (toks cooperEx).reverse).length = 823 := by
  decide +kernel

/-! ### Undecodable input -/

/-- A truncated string goes to the code of the fixed no-instance, one constant-false node. -/
example : outBN [true] = [true, false, false, true, false, false, false, true, false] := by
  decide +kernel

/-- Bits left over after a complete formula make the input undecodable. -/
example : outBN (encodeCNF cooperEx ++ [false]) = encodeRatNet noBN := by
  decide +kernel

/-- A name that is not a canonical `encodeNat` string (the payload `[false]`) makes the input
undecodable. -/
example : outBN [true, false, true, false, true, false, false, true] = encodeRatNet noBN := by
  decide +kernel

/-! ### The main statements at full type -/

/-- The emission writes Cooper's network on every formula. -/
example (φ : Cslib.Logic.LegacyPL.CNF) :
    Cslib.Complexity.Karp.EmitCooper.emitTok (Cslib.Complexity.SatVerifier.toks φ).reverse =
      Cslib.Complexity.Cooper.encodeRatNet (Cslib.Complexity.Cooper.cooperNet φ) := by
  exact emitTok_toks _

/-- The emission equals Cooper's reduction map on every bit string. -/
example (x : List Bool) :
    Cslib.Complexity.Karp.EmitCooper.outBN x = Cslib.Complexity.Cooper.reduceBN x := by
  exact outBN_eq_reduceBN _

end Cslib.Complexity.Karp.EmitCooper.Tests
