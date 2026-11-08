/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Turing computable equals recursive
-/
module

public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
public import MathlibExt.Computability.TuringMachine.Recursive.ToTM2

/-!
# Turing computable equals recursive

The Turing–Kleene equivalence for Mathlib's bundled finite multi-stack machines (the TM2
model): a function `f : ℕ → ℕ` is `Computable` iff some `FinTM2` computes it under the binary
encoding `Computability.encodeNat`.

This discharges the wish `turing_recursive_equiv` (from leanprover/lean-eval, problem
`turing_recursive_equiv`; A. M. Turing, *On Computable Numbers* (1936); S. C. Kleene,
*General recursive functions of natural numbers* (1936)), with the same statement.

## Main results

- `computable_iff_nonempty_tm2Computable` : `Computable f ↔ Nonempty (TM2Computable encodeNat
  encodeNat f)`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt.TM2Recursive

open Computability Turing

/-- **Turing computable equals recursive.** A function `ℕ → ℕ` is recursive iff a bundled
finite multi-stack machine (`FinTM2`) computes it under `encodeNat`. -/
theorem computable_iff_nonempty_tm2Computable (f : ℕ → ℕ) :
    Computable f ↔ Nonempty (TM2Computable encodeNat encodeNat f) :=
  ⟨tm2Computable_of_computable, fun ⟨h⟩ ↦ computable_of_tm2Computable h⟩

end MetaMathlibExt.TM2Recursive
