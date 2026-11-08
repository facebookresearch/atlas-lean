/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Inscribed rectangles in a smooth Jordan curve attain at least one third of all aspect ratios

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.InscribedRectangles` — annals_inscribed_rectangles (manifest `manifests/problems/annals_inscribed_rectangles.toml`, rev 1, submitter Katerina Hristova, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.InscribedRectanglesWanted` namespace. Mathematical
statements are unchanged. Source: C. Hugelmeyer, `Inscribed rectangles in a smooth Jordan curve attain at least one third of all aspect ratios`, Annals of Math, 194 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-2-InscribedRectangles.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Probability.Distributions.Fernique

@[expose] public section

namespace MathlibExt.Geometry.InscribedRectanglesWanted
/-!
# Main Statement from Inscribed rectangles in a smooth Jordan curve attain at least
# one third of all aspect ratios

We formalise the statement of the main result from C. Hugelmeyer, `Inscribed rectangles in a
smooth Jordan curve attain at least one third of all aspect ratios`, Annals of Math, 194 (2) 2021.
-/

set_option autoImplicit false

namespace InscribedRectangles

open Manifold Real MeasureTheory

open scoped ContDiff

/-- Rectangle with sides parallel to the axes, given by opposite corners `a` and `b`. -/
noncomputable def axisAlignedRectangleCorners (a b : ℝ × ℝ) : Fin 4 → ℝ × ℝ :=
  ![(a.1, a.2), (b.1, a.2), (b.1, b.2), (a.1, b.2)]

/-- A rectangle in the Euclidean plane with opposite vertices `a` and `b` rotated by an angle `θ`.
-/
noncomputable def rectangleCorners (a b : ℝ × ℝ) (θ : ℝ) : Fin 4 → ℝ × ℝ :=
  ContinuousLinearMap.rotation θ ∘ axisAlignedRectangleCorners a b

/-- A rectangle is inscribed in a Jordan curve `γ` if all its vertices are distinct and lie on `γ`.
Note: We don't need the smooth hypothesis on the Jordan curve to define this. -/
def IsInscribedRectangle (a b : ℝ × ℝ) (θ : ℝ) (γ : Circle → ℝ × ℝ) : Prop :=
  Function.Injective (rectangleCorners a b θ) ∧ ∀ i : Fin 4, rectangleCorners a b θ i ∈ Set.range γ

/-- The aspect ratio of a rectangle is the ratio of the length of its sides. -/
noncomputable def aspectRatio (a b : ℝ × ℝ) : ℝ :=
  |a.1 - b.1| / |a.2 - b.2|

/-- The set `X` from Theorem 1. More precisely, let `X` be the set of all `r ∈ [0,1]` so that there
is an inscribed rectangle in `γ` of aspect ratio `tan(r·π/4)`. -/
noncomputable def X (γ : Circle → ℝ × ℝ) : Set ℝ :=
  {r : ℝ | r ∈ Set.Icc 0 1 ∧ ∃ a b : ℝ × ℝ, ∃ θ : ℝ,
    aspectRatio a b = tan (r * π / 4) ∧ IsInscribedRectangle a b θ γ}

/--
Statement of Theorem 1:

Let `γ` be a smooth Jordan curve, and let `X` be the set of all `r ∈ [0,1]` so that there is an
inscribed rectangle in `γ` of aspect ratio `tan(r·π/4)`.
Then the Lebesgue measure of `X` is at least `1/3`.
Source: C. Hugelmeyer, `Inscribed rectangles in a smooth Jordan curve attain at least one third of all aspect ratios`, Annals of Math, 194 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-2-InscribedRectangles.lean Via leanprover/lean-eval@38361be, problem `annals_inscribed_rectangles`.
-/
public theorem_wanted theorem_1 (γ : Circle → ℝ × ℝ) (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) :
    volume (X γ) ≥ 1/3

end InscribedRectangles

end MathlibExt.Geometry.InscribedRectanglesWanted
