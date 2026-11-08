/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.CookLevin.Hardness

/-! Tests for the Cook-Levin modules: Horner evaluation, the bit-list converters, and the
headline statements. -/

namespace Cslib.Complexity.CookLevin

open Turing MetaMathlibExt ComplexityTheory Cslib.Complexity.DenseSAT

/-! ### Horner evaluation of the certificate bound -/

/-- `2·3² + 0·3 + 1 = 19`, coefficients highest degree first. -/
example : Precompute.hornVal [2, 0, 1] 3 0 = 19 := rfl

/-- Starting from a nonzero accumulator: `(1·3 + 2)·3 + 0 = 15`. -/
example : Precompute.hornVal [2, 0] 3 1 = 15 := rfl

/-- The Horner value of `p`'s coefficient list is `p.eval`. -/
example (p : Polynomial ℕ) (n : ℕ) : Precompute.hornVal (Precompute.coeffs p) n 0 = p.eval n :=
  Precompute.hornVal_coeffs p n

/-- The `NP` certificate bound enters the tableau width through `mOf`. -/
example (p : Polynomial ℕ) (n : ℕ) : Precompute.mOf p n = n + 1 + p.eval n := rfl

/-! ### The bit-list converters on a real input -/

/-- `DecodeBits` turns the canonical encoding `[true, b, false]` per bit back into the bits. -/
example : ((flip bind (TM2.step DecodeBits.prog))^[6]
    (some (initList DecodeBits.tm
      ((BitstringEncoding.toEncoding (α := List Bool)).encode [true, false])))).map
      (fun c => (c.l, c.stk .out)) = some (none, [true, false]) := rfl

/-- One step earlier it is still emitting. -/
example : ((flip bind (TM2.step DecodeBits.prog))^[5]
    (some (initList DecodeBits.tm
      ((BitstringEncoding.toEncoding (α := List Bool)).encode [true, false])))).map
      (·.l) = some (some .emit) := rfl

/-- `EncodeBits` is the inverse direction. -/
example : ((flip bind (TM2.step EncodeBits.prog))^[6]
    (some (initList EncodeBits.tm [true, false]))).map (fun c => (c.l, c.stk .out)) =
    some (none, (BitstringEncoding.toEncoding (α := List Bool)).encode [true, false]) := by
  decide

/-! ### Headline statements -/

example : denseSatDec ∈ NP := denseSatDec_mem_NP

example (L : DecisionProblem) (hL : L ∈ NP) : Cslib.CookLevin.PolyManyOneRed L denseSatDec :=
  Hardness.denseSatDec_npHard L hL

example : denseSatDec ∈ NP ∧
    ∀ L : DecisionProblem, L ∈ NP → Cslib.CookLevin.PolyManyOneRed L denseSatDec :=
  Hardness.denseSatDec_npComplete

end Cslib.Complexity.CookLevin
