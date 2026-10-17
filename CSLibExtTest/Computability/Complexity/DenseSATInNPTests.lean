/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.DenseSATInNP

namespace Cslib.Complexity.DenseSAT

open Turing MetaMathlibExt ComplexityTheory

/-! ### The canonical pair encoding, concretely -/

/-- `([true], [false])`: six symbols for the bit of `x`, the terminator, three for `w`. -/
example : (BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode ([true], [false]) =
    [true, true, true, true, true, false, false, true, false, false] := rfl

example : (BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode ([], []) =
    [false] := rfl

/-! ### The converter on a real input

`([true, false], [true])`: `2 · 2 + 2 · 1 + 5 = 11` steps to the halting configuration with
`pairEncode` on the output stack; after 10 steps it is still emitting the first component. -/

example : (flip bind Converter.tm.step)^[11]
    (some (initList Converter.tm
      ((BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode
        ([true, false], [true])))) =
    some (haltList Converter.tm (Verifier.pairEncode ([true, false], [true]))) := by
  rw [Converter.initList_tm, Converter.haltList_tm]
  exact Converter.convert_run [true, false] [true]

example : ((flip bind Converter.tm.step)^[11]
    (some (initList Converter.tm
      ((BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode
        ([true, false], [true]))))).map (fun c => (c.l, (c.stk .out : List Verifier.G))) =
    some (none, [.inl true, .inl false, .inr none, .inr (some true)]) := rfl

example : ((flip bind Converter.tm.step)^[10]
    (some (initList Converter.tm
      ((BitstringEncoding.toEncoding (α := List Bool × List Bool)).encode
        ([true, false], [true]))))).map (·.l) = some (some .emitFst) := rfl

/-! ### Membership in the canonical `NP` -/

example : denseSatDec ∈ NP := denseSatDec_mem_NP

example : IsPolyTime (fun p : List Bool × List Bool => check p.1 p.2) := isPolyTime_check

/-- The verifier relation of the membership proof accepts and rejects as expected. -/
example : check [true, false, false, false, true, true, true, false, false, false] [true, true] =
    true := by decide

end Cslib.Complexity.DenseSAT
