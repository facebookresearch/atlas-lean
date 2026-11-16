/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Three-qubit bit-flip code

Basis states are `Fin 8`. Encoding sends `0` to `000` and
`1` to `111`; a single bit flip is xor with a one-hot mask;
recovery is majority vote. Knill-Laflamme conditions are
not included here.
-/

@[expose] public section

/-- Three-qubit bit-flip code (QEC core of QCI-15). Basis
states are `Fin 8`, bits read as `(b₂ b₁ b₀)`. Encoding:
`0 ↦ 000`, `1 ↦ 111`. A single bit flip at position `j`
(xor with `1 <<< j`). Recovery: majority vote to the
nearest codeword basis state. States are amplitude
functions `Fin 8 → ℂ`; all maps act on basis states and
extend linearly because they are precomposition with
basis functions. -/
def encodeQ (b : Fin 2) : Fin 8 := ⟨b.val * 7, by
  have hb := b.isLt
  omega⟩

/-- Bit flip at position `j < 3`. -/
def flipAt (j : Fin 3) (x : Fin 8) : Fin 8 :=
  ⟨x.val ^^^ (1 <<< j.val), by
    have h1 : x.val < 2 ^ 3 := x.isLt
    have h2 : (1 <<< j.val) < 2 ^ 3 := by
      have hj : j.val < 3 := j.isLt
      interval_cases hj' : j.val <;> decide
    exact Nat.xor_lt_two_pow h1 h2⟩

/-- Majority recovery on basis states: count ones; if at
least two, map to `111`, else to `000` (as Fin 8 values
7 and 0). -/
def recoverBasis (x : Fin 8) : Fin 8 :=
  if (x.val.testBit 0).toNat + (x.val.testBit 1).toNat
      + (x.val.testBit 2).toNat ≥ 2
  then ⟨7, by norm_num⟩ else ⟨0, by norm_num⟩

/-- Recovery undoes any single bit flip on codewords. -/
theorem recover_flip_encode (b : Fin 2) (j : Fin 3) :
    recoverBasis (flipAt j (encodeQ b)) = encodeQ b := by
  fin_cases b <;> fin_cases j <;> decide

/-- The encoded logical state: amplitude `φ b` on the
codeword `encodeQ b`, zero elsewhere. -/
def stateOf (φ : Fin 2 → ℂ) : Fin 8 → ℂ :=
  fun x => if x = encodeQ 0 then φ 0 else if x = encodeQ 1 then φ 1 else 0

/-- After a single bit flip and majority recovery, the
logical amplitudes are restored. -/
theorem stateOf_recover_flip (φ : Fin 2 → ℂ) (b : Fin 2) (j : Fin 3) :
    stateOf φ (recoverBasis (flipAt j (encodeQ b))) = φ b := by
  rw [recover_flip_encode]
  fin_cases b <;> simp [stateOf, encodeQ]

end
