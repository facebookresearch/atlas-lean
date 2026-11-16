/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Three-qubit bit-flip code: basis-label correction

The three-qubit bit-flip code encodes the logical basis states `0` and `1` as `000` and
`111`. This file models only the basis labels, as elements of `Fin 8` read as bits
`(b₂ b₁ b₀)`: `encodeQ` sends `0` to `000` and `1` to `111`, `flipAt j` flips bit `j`, and
`recoverBasis` decodes by majority vote. `recover_flip_encode` shows that majority
decoding undoes any single bit flip of a codeword label.

This is the classical (repetition-code) layer of the bit-flip code. Quantum states, error
operators, syndrome measurement, and the recovery of superpositions are not modeled here.
-/

@[expose] public section

namespace MathlibExt.Quantum.BitFlipCode

/-- The codeword label of a logical basis state: `0 ↦ 000` (the label `0`) and
`1 ↦ 111` (the label `7`). -/
def encodeQ (b : Fin 2) : Fin 8 := ⟨b.val * 7, by
  have hb := b.isLt
  omega⟩

/-- Flip bit `j` of a three-bit label, by xor with `1 <<< j`. -/
def flipAt (j : Fin 3) (x : Fin 8) : Fin 8 :=
  ⟨x.val ^^^ (1 <<< j.val), by
    have h1 : x.val < 2 ^ 3 := x.isLt
    have h2 : (1 <<< j.val) < 2 ^ 3 := by
      have hj : j.val < 3 := j.isLt
      interval_cases hj' : j.val <;> decide
    exact Nat.xor_lt_two_pow h1 h2⟩

/-- Majority decoding of a three-bit label: `111` (the label `7`) if at least two bits are
set, and `000` (the label `0`) otherwise. -/
def recoverBasis (x : Fin 8) : Fin 8 :=
  if (x.val.testBit 0).toNat + (x.val.testBit 1).toNat
      + (x.val.testBit 2).toNat ≥ 2
  then ⟨7, by norm_num⟩ else ⟨0, by norm_num⟩

/-- Majority decoding undoes any single bit flip of a codeword label. -/
theorem recover_flip_encode (b : Fin 2) (j : Fin 3) :
    recoverBasis (flipAt j (encodeQ b)) = encodeQ b := by
  fin_cases b <;> fin_cases j <;> decide

end MathlibExt.Quantum.BitFlipCode

end
