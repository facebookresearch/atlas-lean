/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynomial decay rate of y' = -y^3

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.ODE.CubicDecay` — cubic_decay_asymptotic (manifest `manifests/problems/cubic_decay_asymptotic.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.CubicDecayWanted` namespace. Mathematical
statements are unchanged. Source: Standard ODE textbook exercise.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Analysis.CubicDecayWanted
namespace Analysis
namespace ODE

/-!
Polynomial decay of `y' = -y³`.

The differential equation `y'(t) = -(y t)³` with `y 0 = 1` has the explicit solution
`y(t) = 1/√(1 + 2t)` on `[0, ∞)`. This benchmark asks for the asymptotic rate
`y t · √t → 1/√2` as `t → ∞`, given only the ODE and the initial condition.

The interesting content is not the explicit form (a hint) but the asymptotic statement:
the prover must combine an ODE hypothesis with a limit calculation. The ODE pins down `y`
uniquely on `[0, ∞)`, and the asymptotic follows from the closed form.
-/

open Filter Topology

/- Asymptotic decay rate for `y' = -y³, y(0) = 1`: the solution satisfies
`y t · √t → 1/√2` as `t → ∞`. -/
/-- Source: Standard ODE textbook exercise. Via leanprover/lean-eval@38361be, problem `cubic_decay_asymptotic`. -/
public theorem_wanted cubic_decay_asymptotic
    (y : ℝ → ℝ) (hy_diff : ∀ t : ℝ, 0 < t → HasDerivAt y (-(y t) ^ 3) t)
    (hy_cont : ContinuousWithinAt y (Set.Ici 0) 0)
    (hy0 : y 0 = 1) :
    Tendsto (fun t : ℝ => y t * Real.sqrt t) atTop (𝓝 (1 / Real.sqrt 2))

end ODE
end Analysis

end MathlibExt.Analysis.CubicDecayWanted
