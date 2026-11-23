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

/-- **Axis-aligned rectangle.** For points $a = (a_1, a_2)$ and $b = (b_1, b_2)$ of $\mathbb{R}^2$,
the axis-aligned (possibly degenerate) rectangle with opposite corners $a$ and $b$ is the list of
its four vertices $(a_1, a_2)$, $(b_1, a_2)$, $(b_1, b_2)$, $(a_1, b_2)$, in this order. -/
noncomputable def axisAlignedRectangleCorners (a b : ℝ × ℝ) : Fin 4 → ℝ × ℝ :=
  ![(a.1, a.2), (b.1, a.2), (b.1, b.2), (a.1, b.2)]

/-- **Rotated rectangle.** For points $a, b \in \mathbb{R}^2$ and an angle $\theta \in \mathbb{R}$,
the rotated rectangle given by $a$, $b$ and $\theta$ is the list of four points obtained by applying
the rotation $(x, y) \mapsto (x \cos\theta + y \sin\theta, -x \sin\theta + y \cos\theta)$ about the
origin to each vertex, in order, of the axis-aligned rectangle with opposite corners $a$ and $b$.
-/
noncomputable def rectangleCorners (a b : ℝ × ℝ) (θ : ℝ) : Fin 4 → ℝ × ℝ :=
  ContinuousLinearMap.rotation θ ∘ axisAlignedRectangleCorners a b

/-- **Inscribed rectangle.** Let $\gamma$ be a map from the unit circle to $\mathbb{R}^2$. For
points $a, b \in \mathbb{R}^2$ and an angle $\theta \in \mathbb{R}$, the rotated rectangle given by
$a$, $b$ and $\theta$ is inscribed in $\gamma$ when its four vertices are pairwise distinct and
each lies in the image of $\gamma$.

The map $\gamma$ need not be smooth, or even a Jordan curve, for this definition. -/
def IsInscribedRectangle (a b : ℝ × ℝ) (θ : ℝ) (γ : Circle → ℝ × ℝ) : Prop :=
  Function.Injective (rectangleCorners a b θ) ∧ ∀ i : Fin 4, rectangleCorners a b θ i ∈ Set.range γ

/-- **Aspect ratio.** For points $a = (a_1, a_2)$ and $b = (b_1, b_2)$ of $\mathbb{R}^2$, the
aspect ratio of the axis-aligned rectangle with opposite corners $a$ and $b$ is
$|a_1 - b_1| / |a_2 - b_2|$, the ratio of its horizontal side length to its vertical side
length; it is $0$ when $a_2 = b_2$. -/
noncomputable def aspectRatio (a b : ℝ × ℝ) : ℝ :=
  |a.1 - b.1| / |a.2 - b.2|

/-- **Aspect-ratio parameters of inscribed rectangles.** For a map $\gamma$ from the unit circle
to $\mathbb{R}^2$, let $X(\gamma)$ be the set of all $r \in [0, 1]$ for which there are points
$a, b \in \mathbb{R}^2$ and an angle $\theta \in \mathbb{R}$ such that the rotated rectangle given
by $a$, $b$ and $\theta$ is inscribed in $\gamma$ and the axis-aligned rectangle with opposite
corners $a$ and $b$ has aspect ratio $\tan(r\pi/4)$. -/
noncomputable def X (γ : Circle → ℝ × ℝ) : Set ℝ :=
  {r : ℝ | r ∈ Set.Icc 0 1 ∧ ∃ a b : ℝ × ℝ, ∃ θ : ℝ,
    aspectRatio a b = tan (r * π / 4) ∧ IsInscribedRectangle a b θ γ}

/--
**Hugelmeyer's theorem on aspect ratios of inscribed rectangles.** Let $\gamma$ be a smooth Jordan
curve, that is, a map from the unit circle to $\mathbb{R}^2$ that is a $C^\infty$ immersion and a
topological embedding, and let $X$ be the set of all $r \in [0, 1]$ such that some rectangle
inscribed in $\gamma$ has aspect ratio $\tan(r\pi/4)$. Then the Lebesgue measure of $X$ is at
least $1/3$.

Source: C. Hugelmeyer, `Inscribed rectangles in a smooth Jordan curve attain at least one third of all aspect ratios`, Annals of Math, 194 (2) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-2-InscribedRectangles.lean Via leanprover/lean-eval@38361be, problem `annals_inscribed_rectangles`.
-/
public theorem_wanted theorem_1 (γ : Circle → ℝ × ℝ) (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) :
    volume (X γ) ≥ 1/3

end InscribedRectangles

end MathlibExt.Geometry.InscribedRectanglesWanted
