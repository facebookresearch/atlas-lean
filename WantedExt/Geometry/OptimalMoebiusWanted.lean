/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The optimal paper Moebius band

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.OptimalMoebius` — annals_optimal_moebius (manifest `manifests/problems/annals_optimal_moebius.toml`, rev 1, submitter Thomas Browning, Katerina Hristova, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.OptimalMoebiusWanted` namespace. Mathematical
statements are unchanged. Source: R. E. Schwartz, `The optimal paper Moebius band`, Annals of Math, 201 (1) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-1-OptimalMoebius.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MathlibExt.Geometry.OptimalMoebiusWanted
/-!
# Main Statement from The optimal paper Moebius band

We formalise the statement of the main result from R. E. Schwartz, `The optimal paper Moebius band`,
Annals of Math, 201 (1) 2025.
-/

set_option autoImplicit false

namespace OptimalMoebius

open Topology ContDiff

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The set of points `(x, y) ∈ ℝ²` with `0 ≤ x ≤ 1`. -/
abbrev unitStrip : Set ℝ² :=
  {x | x 0 ∈ Set.Icc 0 1}

/-- The map `(x, y) ↦ (1 - x, y + a)`. -/
def period (a : ℝ) : ℝ² → ℝ² :=
  fun x ↦ !₂[1 - x 0, x 1 + a]

/-- The set of points `(x, y) ∈ ℝ²` with `0 ≤ x ≤ 1` and `0 ≤ y < a`. -/
def fundamentalDomain (a : ℝ) : Set ℝ² :=
  {x | x 0 ∈ Set.Icc 0 1 ∧ x 1 ∈ Set.Ico 0 a}

/-- A Moebius embedding is defined in the paper to be a smooth isometric embedding.

We use a function `f` defined on all of `ℝ²`, but only impose conditions on `f` on the unit strip
`[0, 1] × ℝ`. We glue the strip into a Moebius band by imposing `f(1 - x, y + a) = f(x, y)`.

We require the map to be an embedding by requiring injectivity of `f` on a fundamental domain.
We require the embedding to be isometric by requiring the derivative of `f` to be an isometry.
-/
structure IsMoebiusEmbedding (a : ℝ) (f : ℝ² → ℝ³) : Prop where
  periodic : ∀ x ∈ unitStrip, f (period a x) = f x
  smooth : ContDiffOn ℝ ∞ f unitStrip
  isometry : ∀ x ∈ unitStrip, Isometry (fderivWithin ℝ f unitStrip x)
  embedding : Set.InjOn f (fundamentalDomain a)

/--
Statement of Theorem 1.1 (Main):

A smooth embedded paper Moebius band has aspect ratio greater than `√3`.
Source: R. E. Schwartz, `The optimal paper Moebius band`, Annals of Math, 201 (1) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-1-OptimalMoebius.lean Via leanprover/lean-eval@38361be, problem `annals_optimal_moebius`.
-/
public theorem_wanted theorem_1_1 (a : ℝ) (ha : a > 0) (f : ℝ² → ℝ³) (hf : IsMoebiusEmbedding a f) :
    a > √3

end OptimalMoebius

end MathlibExt.Geometry.OptimalMoebiusWanted
