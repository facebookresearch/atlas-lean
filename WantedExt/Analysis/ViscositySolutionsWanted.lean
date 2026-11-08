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

/-- Given `x : Eᴺ` we define `rᵢⱼ = ‖xᵢ - xⱼ‖`. -/
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

/-- We say that a configuration `x : Eᴺ` is without collisions if `rᵢⱼ ≠ 0` for each `i ≠ j`. -/
def WithoutCollisions (x : Eᴺ) : Prop := ∀ i j, i ≠ j → r x i j ≠ 0

/-- Given masses `m : ℝᴺ`, we say that `x : ℝ → Eᴺ` is a solution to the N-body problem if
`x ∈ C²((0,∞))`, `x` is continuous at `0`, and for all `t > 0`, `x'' = ∇ₘ U(x(t))`. -/
structure IsNBodySolution (m : ℝᴺ) (x : ℝ → Eᴺ) where
  contDiff : ContDiffOn ℝ 2 x (Ioi 0)
  continuousAt_zero : ContinuousAt x 0
  eq : ∀ t > 0, iteratedDeriv 2 x t = ∇_[m] (U m) (x t)

end Definitions

/--
Statement of Theorem 1.1:

For any `N`, finite dimensional inner product space `E` of dimension at least `2`,
(positive) masses `m : ℝᴺ`, any initial condition `x₀ : Eᴺ`, any configuration `a : Eᴺ`
without collisions such that `‖a‖ₘ = 1`, and any (positive) energy constant `h`, there exists
(hyperbolic) motions `x : ℝ → Eᴺ` such that they form a solution to the N-body problem with
masses `m`, satisfy the initial condition `x(0) = x₀`, are without collisions for all `t > 0`,
and satisfy

`x(t) = √(2h)ta + o(t)` as `t → ∞`.
Source: E. Maderna and A. Venturelli, `Viscosity solutions and hyperbolic motions: a new PDE method for the N-body problem`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-ViscositySolutions.lean Via leanprover/lean-eval@38361be, problem `annals_viscosity_solutions`.
-/
public theorem_wanted theorem_1_1 (hE : 2 ≤ Module.finrank ℝ E) (m : ℝᴺ) (hm : ∀ i, 0 < m i)
    (x₀ a : Eᴺ) (a_nc : WithoutCollisions a) (a_norm : ‖a‖_[m] = 1) (h : ℝ) (h_pos : h > 0) :
    ∃ x : ℝ → Eᴺ, ∃ o : ℝ → Eᴺ, (o =o[atTop] fun t ↦ t) ∧ x 0 = x₀ ∧
      IsNBodySolution m x ∧ (∀ t > 0, WithoutCollisions (x t)) ∧
        ∀ t ≥ 0, x t = (sqrt (2 * h) * t) • a + o t

end ViscositySolutions

end MathlibExt.Analysis.ViscositySolutionsWanted
