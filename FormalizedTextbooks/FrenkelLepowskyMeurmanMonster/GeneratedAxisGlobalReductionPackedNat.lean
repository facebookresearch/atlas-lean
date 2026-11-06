/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Lean

/-! Long finite-data numerals can be written in short quoted chunks. The macro
only joins decimal digits into an ordinary natural-number literal. All uses
are subsequently checked by Lean's kernel as ordinary arithmetic data. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Join quoted decimal chunks into one ordinary natural-number literal. -/
syntax "generatedAxisGlobalPackedNat%[" str,* "]" : term

macro_rules
  | `(generatedAxisGlobalPackedNat%[$chunks:str,*]) => do
    let digits := String.join (chunks.getElems.toList.map (fun s => s.getString))
    if digits.isEmpty || !digits.toList.all Char.isDigit then
      Lean.Macro.throwError "packed natural data must consist of decimal digits"
    return Lean.Syntax.mkNumLit digits

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
