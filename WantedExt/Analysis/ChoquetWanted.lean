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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.Choquet` — bauer_extreme_point_uniqueness (manifest `manifests/problems/bauer_extreme_point_uniqueness.toml`, rev 1, submitter Kim Morrison, status archived); choquet_representation_theorem (manifest `manifests/problems/choquet_representation_theorem.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.ChoquetWanted` namespace. Mathematical
statements are unchanged. Source: H. Bauer, *Minimalstellen von Funktionen und Extremalpunkte*, Arch. Math. 9 (1958), 389–393; see also Phelps, *Lectures on Choquet's Theorem*. Knill, *Some fundamental theorems in mathematics*, §88. G. Choquet, *Existence et unicité des représentations intégrales au moyen des points extrémaux dans les cônes convexes*, Séminaire Bourbaki (1956). Knill, *Some fundamental theorems in mathematics*, §88.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

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

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/- **Choquet's representation theorem.** Every point `x` of a compact convex
set `K` in a Banach space is the barycenter of a probability measure supported
on the extreme points of `K`: there is a probability measure `μ` with
`μ (ext K)ᶜ = 0` whose barycenter `∫ y, y ∂μ` equals `x`. -/
/-- **Choquet's representation theorem in Banach spaces.** Let $X$ be a real Banach space with its
Borel σ-algebra and let $K \subseteq X$ be compact and convex. For every $x \in K$ there is a
probability measure $\mu$ on $X$ such that the complement of the set of extreme points of $K$ has
$\mu$-measure $0$ and the barycenter $\int y \, d\mu(y)$ (a Bochner integral) equals $x$.

Source: G. Choquet, *Existence et unicité des représentations intégrales au moyen des points extrémaux dans les cônes convexes*, Séminaire Bourbaki (1956). Knill, *Some fundamental theorems in mathematics*, §88. Via leanprover/lean-eval@38361be, problem `choquet_representation_theorem`. -/
public theorem_wanted choquet [MeasurableSpace X] [BorelSpace X]
    (K : Set X) (hK_cpt : IsCompact K) (hK_cvx : Convex ℝ K)
    {x : X} (hx : x ∈ K) :
    ∃ μ : Measure X, IsProbabilityMeasure μ ∧
      μ (K.extremePoints ℝ)ᶜ = 0 ∧
      x = ∫ y, y ∂μ

/- **Bauer's uniqueness at extreme points.** If `x` is an extreme point of a
compact convex set `K` and `μ` is a probability measure supported on `K`
(`μ Kᶜ = 0`) with barycenter `x = ∫ y, y ∂μ`, then `μ` is the Dirac mass at
`x`. (The support hypothesis is the weaker `μ Kᶜ = 0`, making this a
strengthening of the textbook statement: uniqueness among all ambient Borel
probability measures on `K`, not only those already supported on `ext K`.) -/
/-- **Bauer's uniqueness theorem at extreme points.** Let $X$ be a real Banach space with its Borel
σ-algebra, let $K \subseteq X$ be compact and convex, and let $x$ be an extreme point of $K$. If
$\mu$ is a probability measure on $X$ with $\mu(X \setminus K) = 0$ whose barycenter
$\int y \, d\mu(y)$ (a Bochner integral) equals $x$, then $\mu$ is the Dirac measure at $x$.

Source: H. Bauer, *Minimalstellen von Funktionen und Extremalpunkte*, Arch. Math. 9 (1958), 389–393; see also Phelps, *Lectures on Choquet's Theorem*. Knill, *Some fundamental theorems in mathematics*, §88. Via leanprover/lean-eval@38361be, problem `bauer_extreme_point_uniqueness`. -/
public theorem_wanted bauer_unique [MeasurableSpace X] [BorelSpace X]
    (K : Set X) (hK_cpt : IsCompact K) (hK_cvx : Convex ℝ K)
    {x : X} (hx : x ∈ K.extremePoints ℝ)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : μ Kᶜ = 0) (hbar : x = ∫ y, y ∂μ) :
    μ = Measure.dirac x

end Analysis

end MathlibExt.Analysis.ChoquetWanted
