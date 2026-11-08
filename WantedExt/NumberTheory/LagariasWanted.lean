/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lagarias criterion is equivalent to RH

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.Lagarias` — riemann_hypothesis_iff_lagarias_elementary_criterion (manifest `manifests/problems/riemann_hypothesis_iff_lagarias_elementary_criterion.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.LagariasWanted` namespace. Mathematical
statements are unchanged. Source: https://arxiv.org/abs/math/0008177
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

namespace MathlibExt.NumberTheory.LagariasWanted
namespace NumberTheory

open scoped ArithmeticFunction.sigma

/-!
Lagarias' elementary criterion for the Riemann hypothesis.

Mathlib already provides `RiemannHypothesis`, harmonic numbers `harmonic`, and the divisor-sum
function `σ`, so the equivalence can be stated directly.
-/

def LagariasElementaryCriterion : Prop :=
  ∀ n : ℕ,
    0 < n →
      ((σ 1 n : ℕ) : ℝ) ≤
        (harmonic n : ℝ) +
          Real.exp (harmonic n : ℝ) * Real.log (harmonic n : ℝ)

/-- Source: https://arxiv.org/abs/math/0008177 Via leanprover/lean-eval@38361be, problem `riemann_hypothesis_iff_lagarias_elementary_criterion`. -/
public theorem_wanted riemann_hypothesis_iff_lagarias_elementary_criterion :
    RiemannHypothesis ↔ LagariasElementaryCriterion

end NumberTheory

end MathlibExt.NumberTheory.LagariasWanted
