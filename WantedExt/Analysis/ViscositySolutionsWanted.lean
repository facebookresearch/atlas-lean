/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Viscosity solutions and hyperbolic motions: a new PDE method for the N-body problem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.ViscositySolutions` — annals_viscosity_solutions (manifest `manifests/problems/annals_viscosity_solutions.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.ViscositySolutionsWanted` namespace. Mathematical
statements are unchanged. Source: E. Maderna and A. Venturelli, `Viscosity solutions and hyperbolic motions: a new PDE method for the N-body problem`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-ViscositySolutions.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

@[expose] public section

namespace MathlibExt.Analysis.ViscositySolutionsWanted
/-!
# Main Statement from Viscosity solutions and hyperbolic motions:
# a new PDE method for the N-body problem

We formalise the statement of the main result from E. Maderna and A. Venturelli,
`Viscosity solutions and hyperbolic motions: a new PDE method for the N-body problem`,
Annals of Math, 192 (2) 2020.
-/

set_option autoImplicit false

namespace ViscositySolutions

open Filter Gradient Real Set

/- Let `E` be a Euclidean Space. -/
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable {N : ℕ}

local notation "ℝᴺ" => Fin N → ℝ

local notation "Eᴺ" => EuclideanSpace E (Fin N)

section Definitions

/-- **Mutual distances.** For a configuration $x = (x_1, \dots, x_N) \in E^N$ of $N$ points in a
finite-dimensional real inner product space $E$ and indices $i, j$, the mutual distance of the
$i$-th and $j$-th points is $r_{ij}(x) = \lVert x_i - x_j \rVert$. -/
def r (x : Eᴺ) (i j : Fin N) : ℝ := dist (x i) (x j)

/-- Given masses `m : ℝᴺ`, `x : Eᴺ` we define the norm of `x` with respect to the mass scalar
product by `‖x‖ₘ := √(∑ i, mᵢ * ‖xᵢ‖²)`. -/
noncomputable
def weightedNorm (m : ℝᴺ) (x : Eᴺ) : ℝ := sqrt (∑ i, m i * ‖x i‖ ^ 2)

/-- Given masses `m : ℝᴺ`, `f : Eᴺ → ℝ` we define the gradient of `f` with respect to the mass
scalar product by `(∇ₘ f x)ᵢ := mᵢ⁻¹ • (∇ f x)ᵢ` (so that `∇ₘ f x` is the unique vector such that
for any `v : Eᴺ`, `Df(x)(v) = ∑ i, ⟨∇f(x)ᵢ, vᵢ⟩ = ∑ i, mᵢ ⟨∇ₘf(x)ᵢ, vᵢ⟩ = ⟨∇ₘf(x),v⟩ₘ`). -/
noncomputable
def weightedGrad (m : ℝᴺ) (f : Eᴺ → ℝ) (x : Eᴺ) : Eᴺ where
  ofLp i := (m i)⁻¹ • (∇ f x) i

@[inherit_doc] notation "‖" x "‖_["m"]" => weightedNorm m x

@[inherit_doc] notation "∇_["m"]" => weightedGrad m

/-- We define the `Newtonian potential` by the formula:

`U(x) := ∑ i < j, mᵢ * mⱼ * rᵢⱼ⁻¹`. -/
noncomputable
def U (m : ℝᴺ) (x : Eᴺ) : ℝ := ∑ j, ∑ i < j, m i * m j * (r x i j)⁻¹

/-- **Configurations without collisions.** A configuration $x = (x_1, \dots, x_N) \in E^N$ of
$N$ points in a finite-dimensional real inner product space $E$ is without collisions if
$r_{ij}(x) = \lVert x_i - x_j \rVert \neq 0$ for all $i \neq j$. -/
def WithoutCollisions (x : Eᴺ) : Prop := ∀ i j, i ≠ j → r x i j ≠ 0

/-- **Solutions of the $N$-body problem.** Let $E$ be a finite-dimensional real inner product
space, let $N$ be a natural number, give $E^N$ the inner product
$\langle u, v \rangle = \sum_i \langle u_i, v_i \rangle$, and let
$m = (m_1, \dots, m_N) \in \mathbb{R}^N$ be masses. Let
$U(y) = \sum_{i < j} m_i m_j \lVert y_i - y_j \rVert^{-1}$ be the Newtonian potential on $E^N$,
and for $f : E^N \to \mathbb{R}$ let $\nabla_m f(y) \in E^N$ be the mass-weighted gradient, with
components $(\nabla_m f(y))_i = m_i^{-1} (\nabla f(y))_i$, where $\nabla f$ is the gradient of $f$.
A curve $x : \mathbb{R} \to E^N$ is a solution of the $N$-body problem with masses $m$ if $x$ is
$C^2$ on $(0, \infty)$, $x$ is continuous at $0$, and $x''(t) = \nabla_m U(x(t))$ for every
$t > 0$.

In the formalization $0^{-1} = 0$, so a collision term contributes $0$ to $U$ and a zero mass
gives a zero component of $\nabla_m f$. Moreover $\nabla f(y) = 0$ at every point $y$ where $f$
is not differentiable; for instance, a curve that stays at a collision with $x'' = 0$ can be a
solution in this sense. -/
structure IsNBodySolution (m : ℝᴺ) (x : ℝ → Eᴺ) where
  contDiff : ContDiffOn ℝ 2 x (Ioi 0)
  continuousAt_zero : ContinuousAt x 0
  eq : ∀ t > 0, iteratedDeriv 2 x t = ∇_[m] (U m) (x t)

end Definitions

/--
**Maderna–Venturelli theorem on hyperbolic motions.** Let $E$ be a finite-dimensional real
inner product space of dimension at least $2$, let $N$ be a natural number, and let
$m = (m_1, \dots, m_N)$ be positive masses. Let $x_0 \in E^N$, let $a \in E^N$ be a configuration
without collisions with $\lVert a \rVert_m = 1$, where
$\lVert a \rVert_m = \bigl(\sum_i m_i \lVert a_i \rVert^2\bigr)^{1/2}$, and let $h > 0$. Then
there are a solution $x : \mathbb{R} \to E^N$ of the $N$-body problem with masses $m$ and a
function $\varepsilon : \mathbb{R} \to E^N$ with $\lVert \varepsilon(t) \rVert / t \to 0$ as
$t \to \infty$ such that $x(0) = x_0$, the configuration $x(t)$ is without collisions for every
$t > 0$, and $x(t) = \sqrt{2h}\, t\, a + \varepsilon(t)$ for every $t \ge 0$.

Source: E. Maderna and A. Venturelli, `Viscosity solutions and hyperbolic motions: a new PDE method for the N-body problem`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-ViscositySolutions.lean Via leanprover/lean-eval@38361be, problem `annals_viscosity_solutions`.
-/
public theorem_wanted theorem_1_1 (hE : 2 ≤ Module.finrank ℝ E) (m : ℝᴺ) (hm : ∀ i, 0 < m i)
    (x₀ a : Eᴺ) (a_nc : WithoutCollisions a) (a_norm : ‖a‖_[m] = 1) (h : ℝ) (h_pos : h > 0) :
    ∃ x : ℝ → Eᴺ, ∃ o : ℝ → Eᴺ, (o =o[atTop] fun t ↦ t) ∧ x 0 = x₀ ∧
      IsNBodySolution m x ∧ (∀ t > 0, WithoutCollisions (x t)) ∧
        ∀ t ≥ 0, x t = (sqrt (2 * h) * t) • a + o t

end ViscositySolutions

end MathlibExt.Analysis.ViscositySolutionsWanted
