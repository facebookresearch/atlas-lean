/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.Recursive.Equiv

@[expose] public section

/-!
# Tests for the Turing–Kleene equivalence

Machines for concrete recursive functions, and the round trip through both directions.
-/

set_option autoImplicit false

open Computability Turing MetaMathlibExt.TM2Recursive

namespace MathlibExtTest.Computability.TuringMachine.Recursive

/-- The successor function is computed by a `FinTM2`. -/
example : Nonempty (TM2Computable encodeNat encodeNat Nat.succ) :=
  tm2Computable_of_computable Computable.succ

/-- So is `n ↦ n * n`. -/
example : Nonempty (TM2Computable encodeNat encodeNat fun n : ℕ ↦ n * n) :=
  tm2Computable_of_computable (Primrec.nat_mul.comp Primrec.id Primrec.id).to_comp

/-- Round trip: recursive ⇒ Turing computable ⇒ recursive. -/
example (f : ℕ → ℕ) (hf : Computable f) : Computable f :=
  (computable_iff_nonempty_tm2Computable f).2 ((computable_iff_nonempty_tm2Computable f).1 hf)

/-- The wrapped machine for a code evaluating the identity has the identity as its function. -/
example : Nonempty (TM2Computable encodeNat encodeNat (id : ℕ → ℕ)) :=
  ⟨tm2ComputableOfCode ToPartrec.Code.id fun n ↦ by simp⟩

end MathlibExtTest.Computability.TuringMachine.Recursive
