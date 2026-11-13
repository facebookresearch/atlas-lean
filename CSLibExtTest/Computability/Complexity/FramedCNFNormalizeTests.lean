/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.FramedCNF.NormalizeMachine

open Cslib.Complexity.FramedCNF
open NormalizeMachine

example : normalizeNat [] = [] := by decide
example : normalizeNat [false] = [false, true] := by decide
example : normalizeNat [true, false] = [true, false, true] := by decide
example : normalizeNat [false, true] = [false, true] := by decide

-- Execute the actual machine, not only its pure specification.
private def outputAfter (steps : ℕ) (input : List Bool) :=
  ((fun o => o.bind (Turing.TM2.step prog))^[steps]
    (some ⟨some (.read none), false, st input [] []⟩)).map
      (fun c => (c.l, c.stk .output))

example : outputAfter 2 [] = some (some .done, []) := by decide
example : outputAfter 5 [false] =
    some (some .done, [false, true]) := by decide
example : outputAfter 7 [true, false] =
    some (some .done, [true, false, true]) := by decide
example : outputAfter 4 [true] = some (some .done, [true]) := by decide

example : MetaMathlibExt.ComplexityTheory.IsPolyTime normalizeNat :=
  isPolyTime_normalizeNat

example (bits : List Bool) :
    Computability.decodeNat (normalizeNat bits) =
      Computability.decodeNat bits := by
  rw [normalizeNat_eq_encode_decode, Computability.decode_encodeNat]
