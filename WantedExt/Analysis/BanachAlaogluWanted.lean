/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bourbaki's locally convex extension of Banach–Alaoglu

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.BanachAlaoglu` — banach_alaoglu_bourbaki (manifest `manifests/problems/banach_alaoglu_bourbaki.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.BanachAlaogluWanted` namespace. Mathematical
statements are unchanged. Source: N. Bourbaki, Espaces vectoriels topologiques; the normed case is L. Alaoglu, Ann. of Math. 41 (1940). Listed as §137 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.BanachAlaogluWanted
namespace Analysis

/-!
# Bourbaki's locally convex extension of Banach–Alaoglu

§137 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. The classical
Banach–Alaoglu theorem — the closed unit ball of the dual of a Banach space is
weak-star compact — is already in mathlib (`WeakDual.isCompact_closedBall`).
Bourbaki's extension drops the norm: for any real locally convex topological
vector space `E`, the weak-star polar of a neighbourhood of `0` is compact in
the weak dual, extending the statement from closed dual balls to polars of
zero-neighbourhoods in arbitrary locally convex spaces.

mathlib has the normed-space results `WeakDual.isCompact_closedBall` and
`WeakDual.isCompact_polar`, but no corresponding compactness theorem for general
locally convex spaces.
-/

open Set Topology

/-- The weak-star polar of a subset `s` of a real locally convex space `E`:
the continuous functionals `φ` with `‖φ x‖ ≤ 1` for every `x ∈ s`. -/
def weakStarPolar (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] (s : Set E) : Set (WeakDual ℝ E) :=
  {φ | ∀ x ∈ s, ‖φ x‖ ≤ 1}

/- **Bourbaki's locally convex extension of Banach–Alaoglu** (§137). The
weak-star polar of a zero-neighbourhood `U` in a real locally convex space `E`
is weak-star compact. -/
/-- Source: N. Bourbaki, Espaces vectoriels topologiques; the normed case is L. Alaoglu, Ann. of Math. 41 (1940). Listed as §137 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `banach_alaoglu_bourbaki`. -/
public theorem_wanted banach_alaoglu_bourbaki (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (U : Set E) (_hU : U ∈ 𝓝 (0 : E)) :
    IsCompact (weakStarPolar E U)

end Analysis

end MathlibExt.Analysis.BanachAlaogluWanted
