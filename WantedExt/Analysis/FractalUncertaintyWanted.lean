/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fractal uncertainty in higher dimensions

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.FractalUncertainty` — annals_fractal_uncertainty (manifest `manifests/problems/annals_fractal_uncertainty.toml`, rev 1, submitter Justus Springer, Katerina Hristova, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.FractalUncertaintyWanted` namespace. Mathematical
statements are unchanged. Source: A. Cohen, `Fractal uncertainty in higher dimensions`, Annals of Math, 202 (1) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-202-1-FractalUncertainty.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Fourier.LpSpace

@[expose] public section

namespace MathlibExt.Analysis.FractalUncertaintyWanted
/-!
# Main Statement from Fractal uncertainty in higher dimensions

We formalise the statement of the main result from A. Cohen,
`Fractal uncertainty in higher dimensions`, Annals of Math, 202 (1) 2025.
-/

set_option autoImplicit false

namespace FractalUncertainty

open MeasureTheory FourierTransform Metric

open scoped ENNReal

variable {d : ℕ}

local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- We say a set `X ⊂ ℝᵈ` is `ν`-porous on balls from scales `α₀` to `α₁` if, for every ball `B` of
diameter `α₀ < R < α₁`, there is some `x ∈ B` such that `closedBall x (ν * R) ∩ X = ∅`. -/
def PorousOnBalls (ν α₀ α₁ : ℝ) (X : Set ℝᵈ) : Prop :=
  ∀ y, ∀ R ∈ Set.Ioo α₀ α₁, ∃ x ∈ closedBall y (R / 2), closedBall x (ν * R) ∩ X = ∅

/-- We say a set `X` is `ν`-porous on lines from scales `α₀` to `α₁` if for all line segments `τ`
with length `α₀ < R < α₁`, there is some `x ∈ τ` such that `closedBall x (ν * R) ∩ X = ∅`. -/
def PorousOnLines (ν α₀ α₁ : ℝ) (X : Set ℝᵈ) : Prop :=
  ∀ (R : ℝ), R ∈ Set.Ioo α₀ α₁ → ∀ (y₁ y₂ : ℝᵈ), dist y₁ y₂ = R →
    ∃ x ∈ segment ℝ y₁ y₂, closedBall x (ν * R) ∩ X = ∅

/-- Given `a b : ℝ`, the cube `[a,b]ᵈ` in `ℝᵈ`. -/
abbrev cube (a b : ℝ) : Set ℝᵈ := EuclideanSpace.equiv (Fin d) ℝ ⁻¹' Set.univ.pi fun _ ↦ Set.Icc a b

/--
Statement of Theorem 1.1:

Let `ν > 0` and assume that
- `X ⊆ [−1,1]ᵈ` is `ν`-porous on balls from scales `h` to `1`, and
- `Y ⊆ [−h⁻¹,h⁻¹]ᵈ` is `ν`-porous on lines from scales `1` to `h⁻¹`.
Then there exist `β,C > 0` depending only on `ν` and `d` such that for all `f ∈ L²(ℝᵈ)`,
`supp (𝓕 f) ⊆ Y => ‖f * 1_X‖₂ ≤ C * h ^ β * ‖f‖₂`.
Note: We require `X` and `Y` to be measurable to make the statement more natural.
Source: A. Cohen, `Fractal uncertainty in higher dimensions`, Annals of Math, 202 (1) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-202-1-FractalUncertainty.lean Via leanprover/lean-eval@38361be, problem `annals_fractal_uncertainty`.
-/
public theorem_wanted theorem_1_1 (ν : ℝ) (hν₀ : 0 < ν) :
    ∃ (β C : ℝ), β > 0 ∧ C > 0 ∧ ∀ (h : ℝ) (X Y : Set ℝᵈ)
      (hX : MeasurableSet X) (hY : MeasurableSet Y), h ∈ Set.Ioo 0 (1 / 100) →
        X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X → Y ⊆ cube (-h⁻¹) h⁻¹ →
          PorousOnLines ν 1 h⁻¹ Y → ∀ (f : Lp ℂ 2), (𝓕 f : Lp ℂ 2) =ᵐ[volume.restrict Yᶜ] 0 →
            (eLpNorm (X.indicator f) 2).toReal ≤ C * h ^ β * ‖f‖

end FractalUncertainty

end MathlibExt.Analysis.FractalUncertaintyWanted
