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

/-- **Unit strip.** The unit strip is the set of points $(x, y) \in \mathbb{R}^2$ with
$0 \le x \le 1$, that is, $[0, 1] \times \mathbb{R}$. -/
abbrev unitStrip : Set ℝ² :=
  {x | x 0 ∈ Set.Icc 0 1}

/-- **Gluing map of the Moebius band.** For a real number $a$, this is the map
$\mathbb{R}^2 \to \mathbb{R}^2$ given by $(x, y) \mapsto (1 - x, y + a)$. -/
def period (a : ℝ) : ℝ² → ℝ² :=
  fun x ↦ !₂[1 - x 0, x 1 + a]

/-- **Fundamental domain of the Moebius band.** For a real number $a$, this is the set of points
$(x, y) \in \mathbb{R}^2$ with $0 \le x \le 1$ and $0 \le y < a$. -/
def fundamentalDomain (a : ℝ) : Set ℝ² :=
  {x | x 0 ∈ Set.Icc 0 1 ∧ x 1 ∈ Set.Ico 0 a}

/-- **Moebius embedding.** Let $a$ be a real number, let $S = [0, 1] \times \mathbb{R}$ be the
unit strip and let $f : \mathbb{R}^2 \to \mathbb{R}^3$. Then $f$ is a Moebius embedding of
aspect ratio $a$ if $f(1 - x, y + a) = f(x, y)$ for every $(x, y) \in S$, $f$ is $C^\infty$ on
$S$, at every point of $S$ the derivative of $f$ within $S$ is a linear isometry
$\mathbb{R}^2 \to \mathbb{R}^3$, and $f$ is injective on $[0, 1] \times [0, a)$.

This encodes the paper's smooth isometric embedding of a Moebius band: the strip is glued into
a band by the first condition, and injectivity on a fundamental domain makes the glued map an
embedding. -/
structure IsMoebiusEmbedding (a : ℝ) (f : ℝ² → ℝ³) : Prop where
  periodic : ∀ x ∈ unitStrip, f (period a x) = f x
  smooth : ContDiffOn ℝ ∞ f unitStrip
  isometry : ∀ x ∈ unitStrip, Isometry (fderivWithin ℝ f unitStrip x)
  embedding : Set.InjOn f (fundamentalDomain a)

/-- **Schwartz's optimal paper Moebius band theorem.** Let $a > 0$. If
$f : \mathbb{R}^2 \to \mathbb{R}^3$ is a Moebius embedding of aspect ratio $a$, then
$a > \sqrt{3}$. That is, a smooth embedded paper Moebius band has aspect ratio greater
than $\sqrt{3}$.

Source: R. E. Schwartz, `The optimal paper Moebius band`, Annals of Math, 201 (1) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-1-OptimalMoebius.lean Via leanprover/lean-eval@38361be, problem `annals_optimal_moebius`.
-/
public theorem_wanted theorem_1_1 (a : ℝ) (ha : a > 0) (f : ℝ² → ℝ³) (hf : IsMoebiusEmbedding a f) :
    a > √3

end OptimalMoebius

end MathlibExt.Geometry.OptimalMoebiusWanted
