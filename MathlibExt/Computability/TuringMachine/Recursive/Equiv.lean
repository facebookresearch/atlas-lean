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

/-- **Turing computable equals recursive.** A function $f : \mathbb{N} \to \mathbb{N}$ is
computable (recursive) if and only if some bundled finite multi-stack Turing machine computes it
in binary. Here the binary word of $m \in \mathbb{N}$ is its list of binary digits, least
significant first, with $1$ read as true, $0$ as false and no leading zeros (so the word of $0$
is empty). That is, there are such a machine and identifications of its input and output stack
alphabets with the booleans such that, for every $n \in \mathbb{N}$, the machine started at its
main label in its initial internal state, with the binary word of $n$ on its input stack and
every other stack empty, reaches the halted configuration whose output stack holds the binary
word of $f(n)$, whose other stacks are empty and whose internal state is the initial one. -/
theorem computable_iff_nonempty_tm2Computable (f : ℕ → ℕ) :
    Computable f ↔ Nonempty (TM2Computable encodeNat encodeNat f) :=
  ⟨tm2Computable_of_computable, fun ⟨h⟩ ↦ computable_of_tm2Computable h⟩

end MetaMathlibExt.TM2Recursive
