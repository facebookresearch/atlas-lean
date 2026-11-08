/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Real cyclotomic integer with house in (2, 76/33), Real cyclotomic integer with house at most 2

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.SmallHouse` — cyclotomic_integer_house_between_two_and_76_33 (manifest `manifests/problems/cyclotomic_integer_house_between_two_and_76_33.toml`, rev 1, submitter Kim Morrison, status archived); cyclotomic_integer_house_le_two (manifest `manifests/problems/cyclotomic_integer_house_le_two.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.SmallHouseWanted` namespace. Mathematical
statements are unchanged. Source: https://arxiv.org/pdf/1004.0665 https://arxiv.org/pdf/1004.0665
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.House

@[expose] public section

namespace MathlibExt.NumberTheory.SmallHouseWanted
namespace NumberTheory

open NumberField

/-!
Theorem 1.0.5 from Calegari--Morrison--Snyder, "Cyclotomic integers, fusion
categories, and subfactors" (`arXiv:1004.0665`).

Mathlib's `NumberField.house` is exactly the "largest absolute value of all
conjugates" appearing in the paper, so we use it directly.
-/
/-- Source: https://arxiv.org/pdf/1004.0665 Via leanprover/lean-eval@38361be, problem `cyclotomic_integer_house_le_two`. -/
public theorem_wanted cyclotomic_integer_house_le_two
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K] {β : K}
    (hβ_int : IsIntegral ℤ β)
    (hβ_real : β ∈ NumberField.maximalRealSubfield K) :
    house β ≤ 2 →
      house β = 2 ∨ ∃ m : ℕ, 0 < m ∧ house β = 2 * Real.cos (Real.pi / m)

/-- Source: https://arxiv.org/pdf/1004.0665 Via leanprover/lean-eval@38361be, problem `cyclotomic_integer_house_between_two_and_76_33`. -/
public theorem_wanted cyclotomic_integer_house_between_two_and_76_33
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K] {β : K}
    (hβ_int : IsIntegral ℤ β)
    (hβ_real : β ∈ NumberField.maximalRealSubfield K) :
    (2 < house β ∧ house β < (76 : ℝ) / 33) →
      house β = (Real.sqrt 7 + Real.sqrt 3) / 2 ∨
      house β = Real.sqrt 5 ∨
      house β = 1 + 2 * Real.cos (2 * Real.pi / 7) ∨
      house β = (1 + Real.sqrt 5) / Real.sqrt 2 ∨
      house β = (1 + Real.sqrt 13) / 2

end NumberTheory

end MathlibExt.NumberTheory.SmallHouseWanted
