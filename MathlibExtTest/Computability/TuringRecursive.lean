/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Computability.TuringRecursive

open Computability Turing
open MathlibExt.TheoryOfComputation.TuringRecursiveWanted.ModelTheory.TuringRecursive

-- A machine for the constant zero function sends the binary word for two to the empty word.
example : ∃ M : TM2Computable encodeNat encodeNat (fun _ : ℕ ↦ 0),
    Nonempty (TM2Outputs M.tm ([false, true].map M.inputAlphabet.symm) (some [])) := by
  obtain ⟨M⟩ := (turing_recursive_equiv (fun _ ↦ 0)).mp (Computable.const 0)
  exact ⟨M, ⟨M.outputsFun 2⟩⟩

example (f : ℕ → ℕ) (M : TM2Computable encodeNat encodeNat f) : Computable f :=
  (turing_recursive_equiv (f := f)).mpr ⟨M⟩
