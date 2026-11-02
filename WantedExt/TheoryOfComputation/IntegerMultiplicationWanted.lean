/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integer multiplication in time O(n log n)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ModelTheory.IntegerMultiplication` — annals_integer_multiplication (manifest `manifests/problems/annals_integer_multiplication.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.TheoryOfComputation.IntegerMultiplicationWanted` namespace. Mathematical statements are unchanged except for the binary-encoding variant documented below and in the audit table. Source: D. Harvey and J. van der Hoeven, `Integer multiplication in time O(n log n)`, Annals of Math, 193 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-193-2-IntegerMultiplication.lean
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Nat.Digits.Defs

@[expose] public section

namespace MathlibExt.TheoryOfComputation.IntegerMultiplicationWanted
/-!
# Main Statement from Integer multiplication in time O(n log n)

We formalise the statement of the main result from D. Harvey and J. van der Hoeven,
`Integer multiplication in time O(n log n)`, Annals of Math, 193 (2) 2021.

## Implementation Details

The paper works in the "multitape Turing model, in which the time complexity of
an algorithm refers to the number of steps performed by a deterministic Turing
machine with a fixed, finite number of linear tapes". In this formalisation, we
use mathlib's multi-stack machines (TM2), which are equivalent to multitape
machines by an O(1) reduction (use two stacks to simulate one tape).
-/

set_option autoImplicit false

namespace IntegerMultiplication

open Computability Turing Real

/-- **Encoding of pairs.** Given encodings $e_A : A \to \Gamma_A^*$ and $e_B : B \to \Gamma_B^*$
of types $A$ and $B$ as lists over alphabets $\Gamma_A$ and $\Gamma_B$, and a new symbol $\bot$
in neither alphabet, a pair $(a, b)$ is encoded as a list over the alphabet
$(\Gamma_A \cup \{\bot\}) \times (\Gamma_B \cup \{\bot\})$ by zipping: its length is the larger of
the lengths of $e_A(a)$ and $e_B(b)$, and its $i$-th entry is the pair of the $i$-th entries of
$e_A(a)$ and $e_B(b)$, where an entry missing from the shorter list is replaced by $\bot$. -/
def encodeProd {α β αΓ βΓ : Type*} (ea : α → List αΓ) (eb : β → List βΓ) (x : α × β) :
    List (Option αΓ × Option βΓ) :=
  List.zipWithAll Prod.mk (ea x.1) (eb x.2)

/-
Statement of Theorem 1.1:

There is an integer multiplication algorithm achieving `M(n) = O(n log(n))`.
Source: D. Harvey and J. van der Hoeven, `Integer multiplication in time O(n log n)`, Annals of Math, 193 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-193-2-IntegerMultiplication.lean Via leanprover/lean-eval@38361be, problem `annals_integer_multiplication`.
-/
/-- **Binary encoding of natural numbers.** The binary encoding of a natural number $n$ is the
list of its base-$2$ digits, least significant first, with the digit $1$ written as the Boolean
value true and the digit $0$ as false. The list has no trailing zero digit, so $0$ is encoded by
the empty list.

Unlike the unary encoding, this encoding of $n > 0$ has length $\lfloor \log_2 n \rfloor + 1$,
which is the size model of the bit-complexity bound $O(n \log n)$ for integer multiplication;
with the unary encoding that bound could not hold.

Source: Lean variant; this replaces the upstream unary encoding `Computability.encodeNat`. -/
def encodeNatBinary (n : ℕ) : List Bool :=
  (Nat.digits 2 n).map (fun d => d == 1)

/-- **Harvey–van der Hoeven: integer multiplication in time $O(n \log n)$.** There is a
multi-stack Turing machine with finite alphabets and a function $t : \mathbb{N} \to \mathbb{N}$
such that, for all natural numbers $x$ and $y$, the machine started on the encoding of the pair
$(x, y)$ (the binary encodings of $x$ and $y$, zipped) halts within $t(\ell)$ steps with the
binary encoding of $xy$, where $\ell$ is the length of the input, and $t(n) = O(n \log n)$ as
$n \to \infty$.

Source: D. Harvey and J. van der Hoeven, `Integer multiplication in time O(n log n)`, Annals of Math, 193 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-193-2-IntegerMultiplication.lean Via leanprover/lean-eval@38361be, problem `annals_integer_multiplication`. -/
public theorem_wanted theorem_1_1 :
    ∃ T : TM2ComputableInTime (encodeProd encodeNatBinary encodeNatBinary) encodeNatBinary (fun (x, y) ↦ x * y),
      (fun n ↦ (T.time n : ℝ)) =O[Filter.atTop] (fun n ↦ n * log n)

end IntegerMultiplication

end MathlibExt.TheoryOfComputation.IntegerMultiplicationWanted
