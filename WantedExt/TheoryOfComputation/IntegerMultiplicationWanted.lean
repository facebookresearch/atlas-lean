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

/-- Given two encodings `ea` and `eb` of types `α` and `β` in alphabets `αΓ` and `βΓ`, the encoding
of `α × β` in the alphabet `Option αΓ × Option βΓ`. If one encoding is shorter than
the other, the resulting list will be padded with `none` for the shorter list. -/
def encodeProd {α β αΓ βΓ : Type*} (ea : α → List αΓ) (eb : β → List βΓ) (x : α × β) :
    List (Option αΓ × Option βΓ) :=
  List.zipWithAll Prod.mk (ea x.1) (eb x.2)

/-
Statement of Theorem 1.1:

There is an integer multiplication algorithm achieving `M(n) = O(n log(n))`.
Source: D. Harvey and J. van der Hoeven, `Integer multiplication in time O(n log n)`, Annals of Math, 193 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-193-2-IntegerMultiplication.lean Via leanprover/lean-eval@38361be, problem `annals_integer_multiplication`.
-/
/-- Binary encoding of a natural number: its base-2 digits, least
significant first. Its length is `Θ(log n)`, unlike Mathlib's unary
`Computability.encodeNat`; this is the size model of the cited
bit-complexity theorem, and using the unary encoding would make the
stated `O(n log n)` bound uninhabitable. This replaces the upstream unary encoding and is recorded as a Lean variant. -/
def encodeNatBinary (n : ℕ) : List Bool :=
  (Nat.digits 2 n).map (fun d => d == 1)

/-- Source: D. Harvey and J. van der Hoeven, `Integer multiplication in time O(n log n)`, Annals of Math, 193 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-193-2-IntegerMultiplication.lean Via leanprover/lean-eval@38361be, problem `annals_integer_multiplication`. -/
public theorem_wanted theorem_1_1 :
    ∃ T : TM2ComputableInTime (encodeProd encodeNatBinary encodeNatBinary) encodeNatBinary (fun (x, y) ↦ x * y),
      (fun n ↦ (T.time n : ℝ)) =O[Filter.atTop] (fun n ↦ n * log n)

end IntegerMultiplication

end MathlibExt.TheoryOfComputation.IntegerMultiplicationWanted
