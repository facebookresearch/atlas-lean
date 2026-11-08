/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The rectangular peg problem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.RectangularPegProblem` — annals_rectangular_peg_problem (manifest `manifests/problems/annals_rectangular_peg_problem.toml`, rev 1, submitter Katerina Hristova, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.RectangularPegProblemWanted` namespace. Mathematical
statements are unchanged. Source: J. E. Greene and A. Lobb, `The rectangular peg problem`, Annals of Math, 194 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-2-RectangularPegProblem.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Topology.MetricSpace.Similarity

@[expose] public section

namespace MathlibExt.Geometry.RectangularPegProblemWanted
/-!
# Main Statement from The rectangular peg problem

We formalise the statement of the main result from J. E. Greene and A. Lobb,
`The rectangular peg problem`, Annals of Math, 194 (2) 2021.
-/

set_option autoImplicit false

namespace RectangularPegProblem

open Manifold Complex Real

open scoped ContDiff

/-- A rectangle `R` in the complex plane with opposite corners `z` and `w` and rotated by an angle
`θ`. -/
noncomputable def R (z w : ℂ) (θ : Angle) : Fin 4 → ℂ :=
  ![z * θ.toCircle, (w.re + z.im * I) * θ.toCircle, w * θ.toCircle, (z.re + w.im * I) * θ.toCircle]

/--
Statement of Theorem:

For every smooth Jordan curve `γ` and rectangle `R` in the Euclidean plane,
there exists a rectangle similar to `R` whose vertices lie on `γ`.
Note: The paper models the Euclidean plane as the complex plane.
Source: J. E. Greene and A. Lobb, `The rectangular peg problem`, Annals of Math, 194 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-2-RectangularPegProblem.lean Via leanprover/lean-eval@38361be, problem `annals_rectangular_peg_problem`.
-/
public theorem_wanted theorem_1 (γ : Circle → ℂ) (z w : ℂ) (θ : Real.Angle)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℂ) ∞ γ) :
    ∃ (θ' : Real.Angle), ∃ (z' w' : ℂ), Similar (R z w θ) (R z' w' θ') ∧
    ∀ i : Fin 4, R z' w' θ' i ∈ Set.range γ

end RectangularPegProblem

end MathlibExt.Geometry.RectangularPegProblemWanted
