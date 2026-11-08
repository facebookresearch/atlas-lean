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

/-- Given a function `f : E → F` we define the `ℝ≥0∞`-valued `C¹` norm on `s : Set E` by:
`‖f‖_{C¹(s)} := ‖f‖_{L∞(s)} + ‖Df‖_{L∞(s)}`. -/
noncomputable def eC1NormOn [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E]
    (f : E → F) (s : Set E) (μ : Measure E := by volume_tac) : ℝ≥0∞ :=
  eLpNorm f ∞ (μ.restrict s) + eLpNorm (fderiv ℝ f) ∞ (μ.restrict s)

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

/-- Given `f : E → ℝ` and `s : Set E` we define the hessian operator `H` within `s` at `x` as a
linear map from `E` to `E` defined by the identity:

`⟨Hf(x) u, v⟩ = D²f(x) (u,v)`.

where `D²f(x)` is the second Frechet derivative of `f` within `s` at `x` as a bilinear operator. -/
noncomputable def H [CompleteSpace E] (f : E → ℝ) (s : Set E) (x : E) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin (fderivWithin ℝ (fderivWithin ℝ f s) s x)

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Given a linear map `T` from a finite-dimensional inner product space `E` to a finite-dimensional
inner product space `F` we define the Frobenius norm of `T` by `‖T‖_F := √ Trace (T^* ∘ T)`. -/
noncomputable def frobeniusNorm (T : E →L[ℝ] F) : ℝ :=
  √ ((T.toLinearMap.adjoint ∘ₗ T).trace ℝ E)

open Classical in
/-- Given a symmetric linear endomorphism `T` of a finite-dimensional inner product space `E` we
define: `σ₂ T := ∑ i ≤ i < j ≤ n, λᵢ * λⱼ` where `λᵢ` are the eigenvalues of `T`. When `T` is a
non-symmetric linear endomorphism we give it the junk value `0`. -/
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
Statement of Theorem 1.1:

There exists a function `C : ℝ≥0∞ → ℝ` such that if `u : ℝ⁴ → ℝ` satisfies the following properties:
* `u` is smooth on `B₁(0)`,
* `‖u‖_{C¹(B₁(0))} < ∞` (the definition of this norm is given above), and
* for all `x ∈ B₁(0)`, `(Δ u) x > 0` and `(σ₂ D²u) x = 1`,
then `‖D² u 0‖_F ≤ C(‖u‖_{C¹})`.
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
