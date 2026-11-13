/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# General recursive equals Turing computable

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ModelTheory.TuringRecursive` — turing_recursive_equiv (manifest `manifests/problems/turing_recursive_equiv.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.TheoryOfComputation.TuringRecursiveWanted` namespace. Mathematical
statements are unchanged. Source: A. M. Turing, *On Computable Numbers* (1936); S. C. Kleene, *General recursive functions of natural numbers* (1936). Knill, *Some fundamental theorems in mathematics*, §23.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.TheoryOfComputation.TuringRecursiveWanted
namespace ModelTheory.TuringRecursive

/-!
# General recursive = Turing computable

`turing_recursive_equiv`: a total function `f : ℕ → ℕ` is recursive
(`Computable`) iff it is computed by some Turing machine (mathlib's `FinTM2`
model) under Mathlib's unary `Computability.encodeNat` encoding of `ℕ`. This is the Turing–Kleene
equivalence. Mathlib has both predicates and the forward direction via
`tr_eval`, but no theorem linking them; the converse (TM-computable ⇒ recursive)
is absent. Category-(b) candidate from §23 of the Knill survey.
-/

open Computability Turing

/- **General recursive = Turing computable** (total form). A total function
`f : ℕ → ℕ` is recursive (`Computable`, i.e. partial recursive as a partial
function) **iff** it is computed by some Turing machine (mathlib's `FinTM2`
model) under Mathlib's unary `Computability.encodeNat` encoding of `ℕ`. This is Knill's class
equality; the backward direction (TM-computable ⇒ recursive) is absent from
mathlib. -/
/-- **Recursive functions are the Turing-computable functions.** A function
$f : \mathbb{N} \to \mathbb{N}$ is computable, that is, total recursive, if and only if some finite
multi-stack Turing machine computes it on binary representations: there are a machine with
finitely many stacks, internal states and program labels and bijections from its input and output
stack alphabets to $\{0, 1\}$ such that, for every $n \in \mathbb{N}$, the machine started in its
initial state with the binary representation of $n$ (least significant bit first, with $0$
written as the empty word) on its input stack and all other stacks empty halts with the binary
representation of $f(n)$ on its output stack, all other stacks empty and its internal state back
at the initial state.

Source: A. M. Turing, *On Computable Numbers* (1936); S. C. Kleene, *General recursive functions of natural numbers* (1936). Knill, *Some fundamental theorems in mathematics*, §23. Via leanprover/lean-eval@38361be, problem `turing_recursive_equiv`. -/
public theorem_wanted turing_recursive_equiv (f : ℕ → ℕ) :
    Computable f ↔ Nonempty (TM2Computable encodeNat encodeNat f)

end ModelTheory.TuringRecursive

end MathlibExt.TheoryOfComputation.TuringRecursiveWanted
