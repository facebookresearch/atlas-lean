/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite-time singularity formation for C^{1,α} solutions to the incompressible Euler equations on ℝ³

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.FiniteTimeSingularity` — annals_finite_time_singularity (manifest `manifests/problems/annals_finite_time_singularity.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.FiniteTimeSingularityWanted` namespace. Mathematical
statements are unchanged. Source: T. M. Elgindi, `Finite-time singularity formation for C^{1,α} solutions to the incompressible Euler equations on ℝ³`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-FiniteTimeSingularity.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Holder

@[expose] public section

namespace MathlibExt.Analysis.FiniteTimeSingularityWanted
/-!
# Main Statement from Finite-time singularity formation for C^{1,α} solutions to
# the incompressible Euler equations on ℝ³

We formalise the statement of the main result from T. M. Elgindi,
`Finite-time singularity formation for C^{1,α} solutions to the incompressible
Euler equations on ℝ³`, Annals of Math, 194 (3) 2021.
-/

set_option autoImplicit false

section

open NNReal Bornology

variable {α β : Type*} [Bornology α]

/-- We say that a function `f` is bounded on a set `s` if the image of `s` under `f` is bounded. -/
abbrev IsBoundedFunOn (f : β → α) (s : Set β) : Prop := IsBounded (f '' s)

/-- We say that a function `f` is bounded if its range is bounded. -/
abbrev IsBoundedFun (f : β → α) : Prop := IsBoundedFunOn f Set.univ

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

/-- We say that a function `f : X → Y` is `r-Hölder` if there exists `C ≥ 0`, such that
for all `x₁, x₂ : X`, `d_Y(f x₁, f x₂) ≤ C * d_X(x₁, x₂) ^ r`. -/
abbrev Holder (r : ℝ≥0) (f : X → Y) : Prop := ∃ C : ℝ≥0, HolderWith C r f

/-- We say that a function `f : X → Y` is `r-Hölder` on `s : Set X` if there exists `C ≥ 0`, such
that for all `x₁, x₂ ∈ s`, `d_Y(f x₁, f x₂) ≤ C * d_X(x₁, x₂) ^ r`. -/
abbrev HolderOn (r : ℝ≥0) (f : X → Y) (s : Set X) : Prop := ∃ C : ℝ≥0, HolderOnWith C r f s

variable (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- We say that a function `f : E → F` is in `C^{1,α}(E)` if `f` is continuously differentiable,
and `Df` is bounded and `α`-Hölder. -/
def IsContDiffHolder (α : ℝ≥0) (f : E → F) : Prop :=
  ContDiff 𝕜 1 f ∧ IsBoundedFun (fderiv 𝕜 f) ∧ Holder α (fderiv 𝕜 f)

/-- For `s ⊆ E`, we say that a function `f : E → F` is in `C^{1,α}(s)` if `f` is continuously
differentiable, and `Df` is bounded and `α`-Hölder on `s`. -/
def IsContDiffHolderOn (α : ℝ≥0) (f : E → F) (s : Set E) : Prop :=
  ContDiffOn 𝕜 1 f s ∧ IsBoundedFunOn (fderivWithin 𝕜 f s) s ∧ HolderOn α (fderivWithin 𝕜 f s) s

end

namespace FiniteTimeSingularity

open Set Gradient Matrix Filter Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Given functions `v u : ℝ³ → ℝ → ℝ³`, we define the (spatial) directional derivative `u · ∇ₓ v`
of `v` in the direction of `u` by the formula: `Dₓv(x,t)[u(x,t)]`. -/
noncomputable def directionalDeriv (v : ℝ³ → ℝ → ℝ³) (u : ℝ³ → ℝ → ℝ³) (x : ℝ³) (t : ℝ) : ℝ³ :=
  fderiv ℝ (v · t) x (u x t)

local notation u "·∇ₓ" v => directionalDeriv v u

/-- Given a function `u : ℝ³ → ℝ → ℝ³`, we define the derivative with respect to time:
`∂ₜ u x t`. -/
noncomputable def timeDeriv (u : ℝ³ → ℝ → ℝ³) (x : ℝ³) (t : ℝ) : ℝ³ :=
  deriv (u x) t

local notation "∂ₜ" u => timeDeriv u

/-- Given a function `p : ℝ³ → ℝ → ℝ`, we define the (spatial) gradient: `∇ₓ p x t`. -/
noncomputable def spaceGrad (p : ℝ³ → ℝ → ℝ) (x : ℝ³) (t : ℝ) : ℝ³ :=
  ∇ (p · t) x

local notation "∇ₓ" p => spaceGrad p

/-- Given a function `u : ℝ³ → ℝ³` we define its divergence as `trace (Du)`. -/
noncomputable def div (u : ℝ³ → ℝ³) (x : ℝ³) : ℝ :=
  (fderiv ℝ u x).trace ℝ ℝ³

/-- `e i` is the `i`th standard basis vector in `ℝ³`. -/
def e (i : Fin 3) : ℝ³ := WithLp.toLp 2 (Pi.single i 1)

/-- We define the vorticity `∇ × u` of a vector field `u : ℝ³ → ℝ³` to be its curl.
This is given by the formula: `∑ (e i) ×₃ ∂ᵢ u` (where `×₃` is the cross product). -/
noncomputable def vorticity (u : ℝ³ → ℝ³) (x : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (∑ i, e i ⨯₃ (fderiv ℝ u x (e i)))

local notation "∇×" u => vorticity u

/-- We say that `u` is a local solution to the incompressible Euler equation up to time `T`,
with pressure `p` and initial vector field `u₀`, if `u` and `p` are continuously differentiable,
`∂ₜ u + (u ·∇ₓ u) + ∇ₓ p = 0` and `div u = 0` on `ℝ³ × (0,T)` and `u|ₜ₌₀ = u₀`. -/
structure IsLocalEulerEquationSolution
    (p : ℝ³ → ℝ → ℝ) (u₀ : ℝ³ → ℝ³) (T : ℝ) (u : ℝ³ → ℝ → ℝ³) where
  solContDiff : ContDiffOn ℝ 1 u.uncurry (univ ×ˢ Ico 0 T)
  pressureContDiff : ContDiffOn ℝ 1 p.uncurry (univ ×ˢ Ico 0 T)
  eq : ∀ x, ∀ t ∈ Ioo 0 T, (∂ₜ u) x t + (u ·∇ₓ u) x t + (∇ₓ p) x t = 0
  div_free : ∀ t ∈ Ioo 0 T, div (u · t) = 0
  init : (u · 0) = u₀

/-- We say that a vector field `u : ℝ³ → ℝ³` is odd if for each `i`, `uᵢ` is an odd function
of the `i`th coordinate, and an even function of the other two coordinates. -/
def IsOdd (u : ℝ³ → ℝ³) : Prop :=
  (∀ x₁ x₂, (u !₂[·, x₁, x₂] 0).Odd ∧ (u !₂[·, x₁, x₂] 1).Even ∧ (u !₂[·, x₁, x₂] 2).Even) ∧
  (∀ x₀ x₂, (u !₂[x₀, ·, x₂] 0).Even ∧ (u !₂[x₀, ·, x₂] 1).Odd ∧ (u !₂[x₀, ·, x₂] 2).Even) ∧
  (∀ x₀ x₁, (u !₂[x₀, x₁, ·] 0).Even ∧ (u !₂[x₀, x₁, ·] 1).Even ∧ (u !₂[x₀, x₁, ·] 2).Odd)

/--
Statement of Theorem 1:

There exist an `α > 0` and a divergence-free and odd `u₀ ∈ C^{1,α}(ℝ³)` with initial vorticity
`‖∇ × u₀‖ ≤ C/(‖x‖^α + 1)` for some constant `C > 0` so that the unique local odd solution to
(1.1)-(1.3) belonging to the class `C^{1,α}(ℝ³ × [0,1))` satisfies

`lim_{t → 1⁻} ∫ s ∈ [0,t], ‖(∇ × u)(·, s)‖_{L∞} ds = +∞`.

Note: As mentioned in the paper, uniqueness of solutions up until any time `T` (when they exist)
was already known, so the formal statement only asks for existence.
Source: T. M. Elgindi, `Finite-time singularity formation for C^{1,α} solutions to the incompressible Euler equations on ℝ³`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-FiniteTimeSingularity.lean Via leanprover/lean-eval@38361be, problem `annals_finite_time_singularity`.
-/
public theorem_wanted theorem_1 :
    ∃ α > 0, ∃ u₀, div u₀ = 0 ∧ IsOdd u₀ ∧ IsContDiffHolder ℝ α u₀ ∧
      (∃ C > 0, ∀ x, ‖(∇×u₀) x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)) ∧
        ∃ p, ∃ u, (∀ t ∈ Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T ∈ Ioo 0 1, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 T)) ∧
                Tendsto (fun t ↦ ∫ s in 0..t, ⨆ x, ‖(∇×(u · s)) x‖) (𝓝[<] 1) atTop

end FiniteTimeSingularity

end MathlibExt.Analysis.FiniteTimeSingularityWanted
