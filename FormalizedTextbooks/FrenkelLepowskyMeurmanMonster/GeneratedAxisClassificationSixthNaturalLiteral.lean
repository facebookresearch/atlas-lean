/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
import Lean

/-! Long displayed hexadecimal certificate data elaborate to ordinary natural-number literals.
Subsequent kernel proofs compare those literals with the original mathematical definitions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Concatenate displayed hexadecimal chunks into an ordinary Lean numeral term. -/
syntax "sixthHex% " "[" str,* "]" : term

macro_rules
  | `(sixthHex% [$chunks:str,*]) => do
    let mut value : Nat := 0
    for chunk in chunks.getElems do
      for c in chunk.getString.toList do
        let digit ← if '0' ≤ c && c ≤ '9' then
            pure (c.toNat - '0'.toNat)
          else if 'a' ≤ c && c ≤ 'f' then
            pure (c.toNat - 'a'.toNat + 10)
          else
            Lean.Macro.throwErrorAt chunk "Expected lowercase hexadecimal digits"
        value := 16 * value + digit
    return Lean.Syntax.mkNumLit (toString value)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
