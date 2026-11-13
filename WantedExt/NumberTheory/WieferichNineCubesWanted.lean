/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Wieferich's theorem g(3) = 9

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.WieferichNineCubes` — wieferich_g_three (manifest `manifests/problems/wieferich_g_three.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.WieferichNineCubesWanted` namespace. Mathematical
statements are unchanged. Source: A. Wieferich, *Beweis des Satzes, daß sich eine jede ganze Zahl als Summe von höchstens neun positiven Kuben darstellen läßt*, Math. Ann. 66 (1909); A. Kempner, *Über das Waringsche Problem und einige Verallgemeinerungen*, Math. Ann. 72 (1912). Knill, *Some fundamental theorems in mathematics*, §76.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.WieferichNineCubesWanted
namespace NumberTheory

/-!
# Wieferich's theorem `g(3) = 9`

`wieferich_g_three` is Wieferich's theorem (Wieferich 1909, completed by
Kempner 1912): every natural number is a sum of nine cubes, and nine is the
smallest such bound — `23` requires nine cubes (`23 = 2·2³ + 7·1³`, with no
representation using eight or fewer cubes). This is the `k = 3` case of the
Hilbert–Waring problem (`g(3) = 9`).

Mathlib has Lagrange's four-square theorem (`Nat.sum_four_squares`) but no
Hilbert–Waring material: no `g(k)`, no "sum of `k` cubes" predicate, and no
`g(3) = 9`. The trusted helper `IsSumOfCubes` (a non-hole) fixes the meaning of
"sum of `k` cubes".

This is a category-(b) candidate from §76 of the Knill survey
(`sections/076-four-square-theorem.md`).
-/

/-- **Sum of $k$ cubes.** A natural number $n$ is a sum of $k$ cubes if there are natural numbers
$x_1, \dots, x_k$ with $n = x_1^3 + \dots + x_k^3$. -/
def IsSumOfCubes (k n : ℕ) : Prop :=
  ∃ x : Fin k → ℕ, ∑ i, (x i) ^ 3 = n

/- **Wieferich's theorem `g(3) = 9`.** Every natural number is a sum of nine
cubes, and nine is necessary: some `n` (namely `23`) is not a sum of eight
cubes. -/
/-- **Wieferich's nine cubes theorem.** Every natural number is a sum of $9$ cubes of natural
numbers, and $9$ cannot be replaced by $8$: some natural number is not a sum of $8$ cubes of
natural numbers.

Source: A. Wieferich, *Beweis des Satzes, daß sich eine jede ganze Zahl als Summe von höchstens neun positiven Kuben darstellen läßt*, Math. Ann. 66 (1909); A. Kempner, *Über das Waringsche Problem und einige Verallgemeinerungen*, Math. Ann. 72 (1912). Knill, *Some fundamental theorems in mathematics*, §76. Via leanprover/lean-eval@38361be, problem `wieferich_g_three`. -/
public theorem_wanted wieferich_g_three :
    (∀ n : ℕ, IsSumOfCubes 9 n) ∧ ∃ n : ℕ, ¬ IsSumOfCubes 8 n

end NumberTheory

end MathlibExt.NumberTheory.WieferichNineCubesWanted
