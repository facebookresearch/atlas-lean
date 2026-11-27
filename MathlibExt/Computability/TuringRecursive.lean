/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/ModelTheory/TuringRecursive.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `turing_recursive_equiv`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter)
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

The adapted portion is the statement of `turing_recursive_equiv`, moved with its ATLAS
namespace and docstring from `WantedExt/TheoryOfComputation/TuringRecursiveWanted.lean`.
-/
module

public import MathlibExt.Computability.TuringMachine.Recursive.Equiv

/-!
# Recursive functions and Turing machines

`turing_recursive_equiv` characterizes total recursive functions on the natural numbers
by finite multi-stack Turing machines acting on binary words.
-/

public section

namespace MathlibExt.TheoryOfComputation.TuringRecursiveWanted
namespace ModelTheory.TuringRecursive

open Computability Turing

/-- **Recursive functions are the Turing-computable functions.** A function
$f : \mathbb{N} \to \mathbb{N}$ is computable, that is, total recursive, if and only if some finite
multi-stack Turing machine computes it on binary representations: there are a machine with
finitely many stacks, internal states and program labels and bijections from its input and output
stack alphabets to $\{0, 1\}$ such that, for every $n \in \mathbb{N}$, the machine started in its
initial state with the binary representation of $n$ (least significant bit first, with $0$
written as the empty word) on its input stack and all other stacks empty halts with the binary
representation of $f(n)$ on its output stack, all other stacks empty and its internal state back
at the initial state.

Source: A. M. Turing, *On Computable Numbers* (1936); S. C. Kleene, *General recursive functions of
natural numbers* (1936). Knill, *Some fundamental theorems in mathematics*, §23. Via
leanprover/lean-eval@38361be, problem `turing_recursive_equiv`. -/
theorem turing_recursive_equiv (f : ℕ → ℕ) :
    Computable f ↔ Nonempty (TM2Computable encodeNat encodeNat f) :=
  MetaMathlibExt.TM2Recursive.computable_iff_nonempty_tm2Computable f

end ModelTheory.TuringRecursive

end MathlibExt.TheoryOfComputation.TuringRecursiveWanted
