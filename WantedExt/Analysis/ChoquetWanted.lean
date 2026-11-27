/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bauer's uniqueness at extreme points, Choquet's representation theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.Choquet` —
bauer_extreme_point_uniqueness (manifest `manifests/problems/bauer_extreme_point_uniqueness.toml`,
rev 1, submitter Kim Morrison, status archived); choquet_representation_theorem (manifest
`manifests/problems/choquet_representation_theorem.toml`, rev 1, submitter Kim Morrison, status
archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.ChoquetWanted` namespace. Mathematical
statements are unchanged. Source: H. Bauer, *Minimalstellen von Funktionen und Extremalpunkte*,
Arch. Math. 9 (1958), 389–393; see also Phelps, *Lectures on Choquet's Theorem*. Knill, *Some
fundamental theorems in mathematics*, §88. G. Choquet, *Existence et unicité des représentations
intégrales au moyen des points extrémaux dans les cônes convexes*, Séminaire Bourbaki (1956).
Knill, *Some fundamental theorems in mathematics*, §88.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib
public import MathlibExt.Analysis.Convex.Choquet

@[expose] public section

namespace MathlibExt.Analysis.ChoquetWanted
namespace Analysis

/-!
# Choquet's representation theorem and Bauer's uniqueness

`choquet` is Choquet's representation theorem (Choquet 1956): in a Banach space,
every point of a compact convex set `K` is the barycenter `x = ∫ y ∂μ` of a
probability measure `μ` supported on the extreme points of `K`. `bauer_unique`
is Bauer's uniqueness at extreme points: if `x` is an extreme point of `K` and
`μ` is a probability measure on `K` with barycenter `x`, then `μ` is the Dirac
mass at `x`.

A norm-compact set in a Banach space is metrizable, so the extreme points form
a Borel set and Choquet's theorem proper applies (no Choquet–Bishop–de Leeuw
boundary-measure refinement is needed) — the literal "supported on `ext K`"
rendering `μ (K.extremePoints ℝ)ᶜ = 0` is faithful in this setting.

Mathlib has the Krein–Milman theorem (`closure_convexHull_extremePoints`) and
the barycenter-in-convex-set lemma (`Convex.integral_mem`), but neither
Choquet's theorem nor Bauer's uniqueness, and no measure-theoretic barycenter
operator. Both statements use no new definitions beyond Mathlib's
`Set.extremePoints`, `IsProbabilityMeasure`, and the Bochner integral.

These are category-(b) candidates from §88 of the Knill survey
(`sections/088-choquet-theory.md`). (Krein–Milman, the section's other
statement, is category-(a) — already in Mathlib — and is not a candidate.)
-/

open MeasureTheory

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

end Analysis

end MathlibExt.Analysis.ChoquetWanted
