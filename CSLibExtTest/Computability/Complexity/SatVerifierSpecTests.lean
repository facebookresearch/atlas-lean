/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.SatVerifierSpec
public meta import CSLibExt.Computability.Complexity.SatVerifierSpec

/-! Tests for the SAT verifier's stack formats and component specs. -/
namespace Cslib.Complexity.SatVerifier.Tests

open Cslib.CookLevin Cslib.Logic.PL Computability

/-- `(x₁ ∨ ¬x₂) ∧ ¬x₁`: variable `1` occurs twice. -/
private def φ : CNF := [[(1, true), (2, false)], [(1, false)]]

-- Token stack: the reversed reading order; name `1` is `[true]`, name `2` is `[false, true]`.
#guard (toks φ).reverse = [.cl, .lit false, .bit true, .cl, .lit false, .bit true, .bit false,
  .lit true, .bit true]

-- Table stack: one entry per occurrence; the witness `[true, false]` runs out at the third.
#guard tblStk (ents φ [true, false]) = [.dead, .bit true, .val false, .bit true, .bit false,
  .val true, .bit true]

-- `x₁ = true` from its first entry; its third entry is dead.
#guard liveVal (ents φ [true, false]) (encodeNat 1) = true
-- First occurrence wins: `false` from the first entry, though the third says `true`.
#guard liveVal (ents φ [false, true, true]) (encodeNat 1) = false
-- No witness: every entry is dead, so the default `false`.
#guard liveVal (ents φ []) (encodeNat 1) = false

-- The composed spec matches `satVerifier` on short, exact and long witnesses.
#guard [[], [true], [false], [true, false], [false, false], [false, true, false],
    [true, true, true, true], [false, false, false]].all fun w =>
  (satVerifier (encodeCNF φ, w)).ret ==
    ((decodeCNF (encodeCNF φ)).map fun ψ => checkSpec ψ (ents ψ w)).getD false

-- Only `x₁ = x₂ = false` satisfies the formula.
#guard (satVerifier (encodeCNF φ, [false, false, false])).ret && !(satVerifier (encodeCNF φ,
  [true, false, true])).ret

-- A non-canonical name (`[true, false]`, a trailing `false`) is rejected by `tokenize`;
-- the canonical `[false, true]` (variable `2`) is accepted.
#guard tokenize [true, false, true, false, true, true, true, false, false, true] [] = none
#guard tokenize [true, false, true, false, true, false, true, true, false, true] [] =
  some ((toks [[(2, true)]]).reverse, tblStk (ents [[(2, true)]] []))

#guard encodeNat (decodeNat [true, false]) ≠ [true, false] ∧
  encodeNat (decodeNat [false, true]) = [false, true]

end Cslib.Complexity.SatVerifier.Tests
