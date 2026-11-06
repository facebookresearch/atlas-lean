/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Morley's categoricity theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ModelTheory.MorleyCategoricity` — morley_categoricity_theorem (manifest `manifests/problems/morley_categoricity_theorem.toml`, rev 1, submitter A. M. Berns, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.ModelTheory.MorleyCategoricityWanted` namespace. Mathematical
statements are unchanged. Source: M. Ramsey, *Morley's Categoricity Theorem* (UChicago VIGRE REU 2010), Corollary 7.3. https://www.math.uchicago.edu/~may/VIGRE/VIGRE2010/REUPapers/RamseyN.pdf
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.ModelTheory.Satisfiability

@[expose] public section

namespace MathlibExt.ModelTheory.MorleyCategoricityWanted
namespace ModelTheory

open Cardinal

/-!
Morley's categoricity theorem.

A complete theory in a countable language, all of whose models are infinite, that is
categorical in some uncountable cardinal is categorical in every uncountable cardinal.  -/

/-- **Morley's categoricity theorem.** Let $L$ be a first-order language with at most countably
many symbols, and let $T$ be a complete $L$-theory all of whose models are infinite. Call $T$
$\kappa$-categorical if any two models of $T$ of cardinality $\kappa$ are isomorphic. If $T$ is
$\kappa$-categorical for some uncountable cardinal $\kappa$, then $T$ is $\mu$-categorical for
every uncountable cardinal $\mu$.

Source: M. Ramsey, *Morley's Categoricity Theorem* (UChicago VIGRE REU 2010), Corollary 7.3. https://www.math.uchicago.edu/~may/VIGRE/VIGRE2010/REUPapers/RamseyN.pdf Via leanprover/lean-eval@38361be, problem `morley_categoricity_theorem`. -/
public theorem_wanted morley_categoricity_theorem
    (L : FirstOrder.Language.{0, 0}) (hL : L.card ≤ ℵ₀)
    (T : L.Theory) (hT : T.IsComplete)
    (hInf : ∀ M : FirstOrder.Language.Theory.ModelType.{0, 0, 0} T, Infinite M)
    {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) (hcat : κ.Categorical T)
    {μ : Cardinal.{0}} (hμ : ℵ₀ < μ) :
    μ.Categorical T

end ModelTheory

end MathlibExt.ModelTheory.MorleyCategoricityWanted
