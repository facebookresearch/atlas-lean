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
/-- **Unit sphere.** For a natural number $d$, the unit sphere
$S^{d-1} = \{x \in \mathbb{R}^d : \|x\| = 1\}$ in $\mathbb{R}^d$, centered at the origin. -/
abbrev S : Set ℝᵈ := Metric.sphere 0 1

/-- **Origin-symmetric set.** A set $K \subseteq \mathbb{R}^d$ is origin-symmetric if $K = -K$,
where $-K = \{-x : x \in K\}$. -/
abbrev IsOriginSymmetric (K : Set ℝᵈ) : Prop :=
  K = -K

/-- **Centrally symmetric set.** A set $K \subseteq \mathbb{R}^d$ is centrally symmetric if there
is a point $p \in \mathbb{R}^d$ such that the translate $K - p = \{x - p : x \in K\}$ is
origin-symmetric, that is, $K - p = -(K - p)$. -/
abbrev IsCentrallySymmetric (K : Set ℝᵈ) : Prop :=
  ∃ p, IsOriginSymmetric (K - {p})

/-- **Center of mass.** The center of mass of a set $K \subseteq \mathbb{R}^d$ is the average
$\frac{1}{\operatorname{vol}(K)} \int_K x \, dx$, where $dx$ is Lebesgue measure on $\mathbb{R}^d$.
By convention it is $0$ when $\operatorname{vol}(K)$ is $0$ or infinite, or when $x \mapsto x$ is
not integrable on $K$. For a compact convex body this is the usual center of mass. -/
noncomputable abbrev centerOfMass (K : Set ℝᵈ) : ℝᵈ := ⨍ x in K, x

/-- **Lower half-space.** For a unit vector $\xi \in \mathbb{R}^d$ and $t \in \mathbb{R}$, the
closed lower half-space is $H^-(\xi) = \{p \in \mathbb{R}^d : \xi \cdot p \le t\}$.

Source: D. Ryabogin, A negative answer to Ulam's Problem 19 from the Scottish Book, Annals of
Math. 195 (3) 2022, Equation (1). -/
def H_minus (ξ : S d) (t : ℝ) : Set ℝᵈ := { x | ⟪x, ξ⟫ ≤ t }

/-- **Cutting hyperplane at a level.** Let $K \subseteq \mathbb{R}^d$, let $\xi \in \mathbb{R}^d$ be
a unit vector and let $\delta \in \mathbb{R}$. A cutting hyperplane of $K$ in direction $\xi$ at
level $\delta$ is a real number $t$, standing for the hyperplane
$\{p \in \mathbb{R}^d : \xi \cdot p = t\}$, such that the volume of
$K \cap \{p \in \mathbb{R}^d : \xi \cdot p \le t\}$ equals $\delta$. Here a set of infinite volume
is assigned volume $0$. -/
structure CuttingHyperplaneAtLevel (K : Set ℝᵈ) (ξ : S d) (δ : ℝ) where
  /-- The translation of the hyperplane. -/
  t : ℝ
  vol : volume.real (K ∩ H_minus ξ t) = δ

/-- **Direction of the line through the centers of mass.** Let $d$ be a natural number, let
$K \subseteq \mathbb{R}^d$, let $\xi$ be a unit vector in $\mathbb{R}^d$, let
$\delta \in \mathbb{R}$, and let $H$ be a cutting hyperplane of $K$ in direction $\xi$ at level
$\delta$, with translation $t$, so that
$H^-(\xi) = \{x \in \mathbb{R}^d : \langle x, \xi \rangle \le t\}$. Writing $c(A)$ for the center
of mass of a set $A \subseteq \mathbb{R}^d$, the direction vector of the line $l(\xi)$ through the
center of mass of $K$ and the center of mass of the submerged part $K \cap H^-(\xi)$ is the vector
$c(K) - c(K \cap H^-(\xi))$. -/
noncomputable def CuttingHyperplaneAtLevel.lineThroughCentersOfMass {K : Set ℝᵈ} {ξ : S d} {δ : ℝ}
    (H : CuttingHyperplaneAtLevel K ξ δ) : ℝᵈ :=
  centerOfMass K - centerOfMass (K ∩ H_minus ξ H.t)

/-- **Floating in equilibrium in a direction.** Let $K \subseteq \mathbb{R}^d$, let
$\xi \in \mathbb{R}^d$ be a unit vector and let $\delta \in \mathbb{R}$. We say that $K$ floats in
equilibrium in direction $\xi$ at level $\delta$ if, for every cutting hyperplane
$\{p : \xi \cdot p = t\}$ of $K$ in direction $\xi$ at level $\delta$, the center of mass of $K$
minus the center of mass of $K \cap \{p : \xi \cdot p \le t\}$ is a real multiple of $\xi$
(possibly zero); that is, the line through the two centers of mass is parallel to $\xi$ when they
differ. -/
def FloatsInEquilibriumInDirectionAtLevel (K : Set ℝᵈ) (ξ : S d) (δ : ℝ) : Prop :=
  ∀ H : CuttingHyperplaneAtLevel K ξ δ, H.lineThroughCentersOfMass ∈ ℝ ∙ ξ.val

/-- **Floating in equilibrium in every orientation.** A set $K \subseteq \mathbb{R}^d$ floats in
equilibrium in every orientation at level $\delta \in \mathbb{R}$ if it floats in equilibrium in
direction $\xi$ at level $\delta$ for every unit vector $\xi \in \mathbb{R}^d$. -/
def FloatsInEquilibriumInEveryOrientationAtLevel (K : Set ℝᵈ) (δ : ℝ) : Prop :=
  ∀ ξ, FloatsInEquilibriumInDirectionAtLevel K ξ δ

/-- **Body of revolution.** A body of revolution in $\mathbb{R}^d$ is given by real numbers
$R_1, R_2$ and a function $f : \mathbb{R} \to \mathbb{R}$ that vanishes outside the interval
$[-R_1, R_2]$, is infinitely differentiable on the open interval $(-R_1, R_2)$ and is concave on
$[-R_1, R_2]$. The dimension $d$ is only a parameter; these data do not depend on it. -/
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

/-- **Solid of revolution.** Let $d \ge 1$ and let a body of revolution in $\mathbb{R}^d$ be given
by $R_1$, $R_2$ and $f$. Writing points of $\mathbb{R}^d$ as $x = (x_0, \dots, x_{d-1})$, its solid
is the set of all $x$ with $x_0 \in [-R_1, R_2]$ and $x_1^2 + \dots + x_{d-1}^2 \le f(x_0)^2$. -/
def BodyOfRevolution.body [NeZero d] (K : BodyOfRevolution d) : Set ℝᵈ :=
  { x | x 0 ∈ Set.Icc (-K.R₁) K.R₂ ∧ ∑ i > 0, (x i) ^ 2 ≤ K.f (x 0) ^ 2 }

/-- **Strictly convex body.** A set $K \subseteq \mathbb{R}^d$ is a strictly convex body if it is
strictly convex (for distinct $x, y \in K$, every point of the open segment between $x$ and $y$
lies in the interior of $K$), compact, and has nonempty interior. -/
def IsStrictlyConvexBody (K : Set ℝᵈ) : Prop :=
  StrictConvex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

/--
**Ryabogin's negative answer to Ulam's floating body problem.** Let $d \ge 3$. There exists a
body of revolution $K \subset \mathbb{R}^d$ that is a strictly convex body, is not centrally
symmetric, and floats in equilibrium in every orientation at the level $\operatorname{vol}(K)/2$.

Source: D. Ryabogin, `A negative answer to Ulam's Problem 19 from the Scottish Book`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-Ulam.lean Via leanprover/lean-eval@38361be, problem `annals_ulam`.
-/
public theorem_wanted theorem_1 (hd : 3 ≤ d) : letI : NeZero d := ⟨by omega⟩
    ∃ K : BodyOfRevolution d, IsStrictlyConvexBody K.body ∧ ¬ IsCentrallySymmetric K.body ∧
      FloatsInEquilibriumInEveryOrientationAtLevel K.body (volume.real K.body / 2)

end Ulam

end MathlibExt.Geometry.UlamWanted
