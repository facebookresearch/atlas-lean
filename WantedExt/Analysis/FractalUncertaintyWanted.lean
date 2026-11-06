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

/-- **Porosity on balls.** Let $d$ be a natural number and let $\nu$, $\alpha_0$ and $\alpha_1$ be
real numbers. A set $X$ in the Euclidean space $\mathbb{R}^d$ is $\nu$-porous on balls from scales
$\alpha_0$ to $\alpha_1$ if for every $y \in \mathbb{R}^d$ and every $R$ with
$\alpha_0 < R < \alpha_1$, the closed ball of radius $R/2$ about $y$ contains a point $x$ such that
the closed ball of radius $\nu R$ about $x$ is disjoint from $X$. -/
def PorousOnBalls (ν α₀ α₁ : ℝ) (X : Set ℝᵈ) : Prop :=
  ∀ y, ∀ R ∈ Set.Ioo α₀ α₁, ∃ x ∈ closedBall y (R / 2), closedBall x (ν * R) ∩ X = ∅

/-- **Porosity on lines.** Let $d$ be a natural number and let $\nu$, $\alpha_0$ and $\alpha_1$ be
real numbers. A set $X$ in the Euclidean space $\mathbb{R}^d$ is $\nu$-porous on lines from scales
$\alpha_0$ to $\alpha_1$ if for every $R$ with $\alpha_0 < R < \alpha_1$ and all points
$y_1, y_2 \in \mathbb{R}^d$ at distance $R$, the closed segment from $y_1$ to $y_2$ contains a point
$x$ such that the closed ball of radius $\nu R$ about $x$ is disjoint from $X$. -/
def PorousOnLines (ν α₀ α₁ : ℝ) (X : Set ℝᵈ) : Prop :=
  ∀ (R : ℝ), R ∈ Set.Ioo α₀ α₁ → ∀ (y₁ y₂ : ℝᵈ), dist y₁ y₂ = R →
    ∃ x ∈ segment ℝ y₁ y₂, closedBall x (ν * R) ∩ X = ∅

/-- **Closed cubes in Euclidean space.** Let $d$ be a natural number. For real numbers $a$ and $b$,
the cube $[a,b]^d$ is the set of points $x$ of the Euclidean space $\mathbb{R}^d$ with
$a \le x_i \le b$ for every coordinate $i$. -/
abbrev cube (a b : ℝ) : Set ℝᵈ := EuclideanSpace.equiv (Fin d) ℝ ⁻¹' Set.univ.pi fun _ ↦ Set.Icc a b

/--
**Cohen's fractal uncertainty principle for line-porous sets.** Let $d$ be a natural number and
$\nu > 0$. Then there are real numbers $\beta > 0$ and $C > 0$ such that for every $h$ with
$0 < h < 1/100$ and all measurable sets $X, Y$ in the Euclidean space $\mathbb{R}^d$ the following
holds: if $X \subseteq [-1,1]^d$ is $\nu$-porous on balls from scales $h$ to $1$ and
$Y \subseteq [-h^{-1},h^{-1}]^d$ is $\nu$-porous on lines from scales $1$ to $h^{-1}$, then every
$f \in L^2(\mathbb{R}^d)$ whose Fourier transform $\mathcal{F}f$ vanishes almost everywhere outside
$Y$ satisfies $\|\mathbf{1}_X f\|_2 \le C h^{\beta} \|f\|_2$. Thus $\beta$ and $C$ depend only on
$\nu$ and $d$.

Here $\mathcal{F}$ is the Fourier transform on $L^2(\mathbb{R}^d)$, extended by continuity from
$\mathcal{F}f(\xi) = \int_{\mathbb{R}^d} e^{-2\pi i \langle x, \xi \rangle} f(x)\,dx$ on Schwartz
functions.

We require $X$ and $Y$ to be measurable to make the statement more natural.

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
