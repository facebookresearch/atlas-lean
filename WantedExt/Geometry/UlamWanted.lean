/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A negative answer to Ulam's Problem 19 from the Scottish Book

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.ConvexGeometry.Ulam` — annals_ulam (manifest `manifests/problems/annals_ulam.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.UlamWanted` namespace. Mathematical
statements are unchanged. Source: D. Ryabogin, `A negative answer to Ulam's Problem 19 from the Scottish Book`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-Ulam.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Geometry.UlamWanted
/-!
# Main Statement from A negative answer to Ulam's Problem 19 from the Scottish Book

We formalise the statement of the main result from D. Ryabogin,
`A negative answer to Ulam's Problem 19 from the Scottish Book`, Annals of Math, 195 (3) 2022.
-/

set_option autoImplicit false

namespace Ulam

open MeasureTheory

open scoped ContDiff Pointwise RealInnerProductSpace

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

variable (d) in
/-- The unit sphere in `ℝᵈ`, centered at the origin. This is denoted `Sᵈ⁻¹` in the paper. -/
abbrev S : Set ℝᵈ := Metric.sphere 0 1

/-- A subset `K ⊆ ℝᵈ` is called origin-symmetric if `K = -K`. -/
abbrev IsOriginSymmetric (K : Set ℝᵈ) : Prop :=
  K = -K

/-- A subset `K ⊆ ℝᵈ` is called centrally symmetric, if there exists `p ∈ ℝᵈ` such that `K - p`
is origin symmetric. -/
abbrev IsCentrallySymmetric (K : Set ℝᵈ) : Prop :=
  ∃ p, IsOriginSymmetric (K - {p})

/-- The center of mass of a `d`-dimensional compact convex set `K ⊆ ℝᵈ` is defined to be
`(1 / vol(K)) * ∫_K x dx`, where `dx` is the usual Lebesgue measure in `ℝᵈ`. -/
noncomputable abbrev centerOfMass (K : Set ℝᵈ) : ℝᵈ := ⨍ x in K, x

/-- Given a direction `ξ ∈ S d` and `t ∈ ℝ`, we define the set
`H⁻(ξ) = { p ∈ ℝᵈ | ξ ∙ p ≤ t }`; see Equation (1) in the paper. -/
def H_minus (ξ : S d) (t : ℝ) : Set ℝᵈ := { x | ⟪x, ξ⟫ ≤ t }

/-- A hyperplane `H(ξ) = { p ∈ ℝᵈ | ξ ∙ p = t }` is called the cutting hyperplane of `K` at
level `δ ∈ ℝ`, if `vol(K ∩ H⁻(ξ)) = δ`. -/
structure CuttingHyperplaneAtLevel (K : Set ℝᵈ) (ξ : S d) (δ : ℝ) where
  /-- The translation of the hyperplane. -/
  t : ℝ
  vol : volume.real (K ∩ H_minus ξ t) = δ

/-- The direction vector of the line `l(ξ)` passing through the center of mass of `K` and the
center of mass of the "submerged part" `K ∩ H⁻(ξ)`. -/
noncomputable def CuttingHyperplaneAtLevel.lineThroughCentersOfMass {K : Set ℝᵈ} {ξ : S d} {δ : ℝ}
    (H : CuttingHyperplaneAtLevel K ξ δ) : ℝᵈ :=
  centerOfMass K - centerOfMass (K ∩ H_minus ξ H.t)

/-- We say that `K` floats in equilibrium in direction `ξ` at level `δ`, if for all cutting
hyperplanes at level `δ`, the line `l(ξ)` through the centers of masses is parallel to `ξ`. -/
def FloatsInEquilibriumInDirectionAtLevel (K : Set ℝᵈ) (ξ : S d) (δ : ℝ) : Prop :=
  ∀ H : CuttingHyperplaneAtLevel K ξ δ, H.lineThroughCentersOfMass ∈ ℝ ∙ ξ.val

/-- We say that `K` floats in equilibrium in every orientation at level `δ`, if it floats
in equilibrium in direction `ξ` at level `δ`, for all `ξ ∈ S^d`. -/
def FloatsInEquilibriumInEveryOrientationAtLevel (K : Set ℝᵈ) (δ : ℝ) : Prop :=
  ∀ ξ, FloatsInEquilibriumInDirectionAtLevel K ξ δ

/-- A body of revolution is given by a smooth concave function `f : ℝ → ℝ` supported on
an interval `[-R₁, R₂]`. -/
structure BodyOfRevolution (d : ℕ) where
  /-- The left half-length of the interval; `f` is supported on `[-R₁, R₂]`. -/
  R₁ : ℝ
  /-- The right half-length of the interval; `f` is supported on `[-R₁, R₂]`. -/
  R₂ : ℝ
  /-- The smooth concave function `f : ℝ → ℝ` defining the body of revolution. -/
  f : ℝ → ℝ
  support : f.support ⊆ Set.Icc (-R₁) R₂
  smooth : ContDiffOn ℝ ∞ f (Set.Ioo (-R₁) R₂)
  concave : ConcaveOn ℝ (Set.Icc (-R₁) R₂) f

/-- The convex body of revolution defined by a smooth concave function `f : ℝ → ℝ` supported on
`[-R₁, R₂]` is `K_f := { x ∈ ℝᵈ | x₁ ∈ [-R₁, R₂] and x₂² + ... + x²_d ≤ f(x₁)² }`.
Note: we actually index the `xᵢ` starting from zero, for convenience. -/
def BodyOfRevolution.body [NeZero d] (K : BodyOfRevolution d) : Set ℝᵈ :=
  { x | x 0 ∈ Set.Icc (-K.R₁) K.R₂ ∧ ∑ i > 0, (x i) ^ 2 ≤ K.f (x 0) ^ 2 }

/-- A strictly convex body `K ⊂ ℝᵈ` is a strictly convex compact set with non-empty interior. -/
def IsStrictlyConvexBody (K : Set ℝᵈ) : Prop :=
  StrictConvex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/--
Statement of Theorem 1:

Let `d ≥ 3`. There exists a strictly convex non-centrally-symmetric body of revolution `K ⊂ ℝᵈ`
that floats in equilibrium in every orientation at the level `vol(K)/2`.
Source: D. Ryabogin, `A negative answer to Ulam's Problem 19 from the Scottish Book`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-Ulam.lean Via leanprover/lean-eval@38361be, problem `annals_ulam`.
-/
public theorem_wanted theorem_1 (hd : 3 ≤ d) : letI : NeZero d := ⟨by omega⟩
    ∃ K : BodyOfRevolution d, IsStrictlyConvexBody K.body ∧ ¬ IsCentrallySymmetric K.body ∧
      FloatsInEquilibriumInEveryOrientationAtLevel K.body (volume.real K.body / 2)

end Ulam

end MathlibExt.Geometry.UlamWanted
