/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Hessian estimates for the sigma-2 equation in dimension four

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.HessianEstimates` — annals_hessian_estimates (manifest `manifests/problems/annals_hessian_estimates.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.HessianEstimatesWanted` namespace. Mathematical
statements are unchanged. Source: R. Shankar and Y. Yuan, `Hessian estimates for the sigma-2 equation in dimension four`, Annals of Math, 201 (2) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-2-HessianEstimates.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.HessianEstimatesWanted
/-!
# Main Statement from Hessian estimates for the sigma-2 equation in dimension four

We formalise the statement of the main result from R. Shankar and Y. Yuan,
`Hessian estimates for the sigma-2 equation in dimension four`, Annals of Math, 201 (2) 2025.
-/

set_option autoImplicit false

namespace HessianEstimates

open Laplacian Metric ContDiff MeasureTheory ENNReal

section Definitions

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-- **C¹ norm on a set.** Let $E$ and $F$ be real normed spaces and let $\mu$ be a measure on $E$
(by default the volume measure). For a function $f : E \to F$ and a set $s \subseteq E$, write
$\mu_s$ for the restriction of $\mu$ to $s$. The $C^1$ norm of $f$ on $s$ is the extended
nonnegative real number
$$\|f\|_{C^1(s)} = \|f\|_{L^\infty(\mu_s)} + \|Df\|_{L^\infty(\mu_s)},$$
where $\|g\|_{L^\infty(\mu_s)}$ is the $\mu_s$-essential supremum of $\|g\|$, and $Df$ is the
Fréchet derivative of $f$ on all of $E$ (taken to be $0$ at points where $f$ is not
differentiable), a function from $E$ to the continuous linear maps $E \to F$, measured in the
operator norm. -/
noncomputable def eC1NormOn [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E]
    (f : E → F) (s : Set E) (μ : Measure E := by volume_tac) : ℝ≥0∞ :=
  eLpNorm f ∞ (μ.restrict s) + eLpNorm (fderiv ℝ f) ∞ (μ.restrict s)

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-- **Hessian operator within a set.** Let $E$ be a real Hilbert space, let $f : E \to \mathbb{R}$,
let $s \subseteq E$ and let $x \in E$. Write $D^2 f(x)$ for the second Fréchet derivative of $f$
within $s$ at $x$, that is, the derivative within $s$ at $x$ of the map sending $y$ to the
derivative of $f$ within $s$ at $y$; it is a continuous bilinear form on $E$. The Hessian
operator of $f$ within $s$ at $x$ is the continuous linear map $Hf(x) : E \to E$ determined by
$\langle Hf(x)\, u, v \rangle = D^2 f(x)(u, v)$ for all $u, v \in E$. -/
noncomputable def H [CompleteSpace E] (f : E → ℝ) (s : Set E) (x : E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ f s) s x)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- **Frobenius norm.** Let $E$ and $F$ be finite-dimensional real inner product spaces. The
Frobenius norm of a continuous linear map $T : E \to F$ is
$\|T\|_F = \sqrt{\operatorname{tr}(T^* T)}$, where $T^* : F \to E$ is the adjoint of $T$ and the
trace is taken on $E$. -/
noncomputable def frobeniusNorm (T : E →L[ℝ] F) : ℝ :=
  √ ((T.toLinearMap.adjoint ∘ₗ T).trace ℝ E)

open Classical in
/-- **Second elementary symmetric function of the eigenvalues.** Let $E$ be a finite-dimensional
real inner product space of dimension $n$. If $T : E \to E$ is a symmetric linear map with
eigenvalues $\lambda_1, \dots, \lambda_n$, listed with multiplicity, then
$\sigma_2(T) = \sum_{1 \le i < j \le n} \lambda_i \lambda_j$. If $T$ is not symmetric, then
$\sigma_2(T) = 0$ by convention. -/
noncomputable def σ₂ (T : E →L[ℝ] E) : ℝ :=
  if hT : T.IsSymmetric then
    ∑ j, ∑ i < j, hT.eigenvalues rfl i * hT.eigenvalues rfl j
  else
    0

end Definitions

local notation "‖" f "‖_C¹(" s ")" => eC1NormOn f s volume

local notation "‖" T "‖_F" => frobeniusNorm T

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

local notation "B₁(0)" => ball 0 1

/--
**Shankar–Yuan Hessian estimate for the sigma-2 equation in dimension four.** There is a function
$C : [0, \infty] \to \mathbb{R}$ with the following property. Let $B_1(0)$ be the open unit ball in
$\mathbb{R}^4$, and let $u : \mathbb{R}^4 \to \mathbb{R}$ be smooth ($C^\infty$) on $B_1(0)$ with
finite $C^1$ norm $\|u\|_{C^1(B_1(0))}$ with respect to Lebesgue measure. Suppose that for every
$x \in B_1(0)$ the Laplacian satisfies $\Delta u(x) > 0$ and the Hessian operator $Hu(x)$ of $u$
within $B_1(0)$ satisfies $\sigma_2(Hu(x)) = 1$, where $\sigma_2$ of a symmetric operator is the
second elementary symmetric function of its eigenvalues and $\sigma_2$ of a non-symmetric operator
is $0$. Then the Frobenius norm of the Hessian operator at the origin satisfies
$\|Hu(0)\|_F \le C(\|u\|_{C^1(B_1(0))})$.

Source: R. Shankar and Y. Yuan, `Hessian estimates for the sigma-2 equation in dimension four`, Annals of Math, 201 (2) 2025. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2025-201-2-HessianEstimates.lean Via leanprover/lean-eval@38361be, problem `annals_hessian_estimates`.
-/
public theorem_wanted theorem_1_1 : ∃ C : ℝ≥0∞ → ℝ, ∀ (u : ℝ⁴ → ℝ)
    (_smooth : ContDiffOn ℝ ∞ u B₁(0))
    (_bounded : ‖u‖_C¹(B₁(0)) < (∞ : ℝ≥0∞))
    (_positive_branch : ∀ x ∈ B₁(0), (Δ u) x > 0)
    (_solution : ∀ x ∈ B₁(0), σ₂ (H u B₁(0) x) = 1),
    ‖H u B₁(0) 0‖_F ≤ C (‖u‖_C¹(B₁(0)))

end HessianEstimates

end MathlibExt.Analysis.HessianEstimatesWanted
