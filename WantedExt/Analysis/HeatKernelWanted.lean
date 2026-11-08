/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Gaussian heat kernel solves the 1D heat equation

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.ODE.HeatKernel` — heat_kernel_solves_heat_equation (manifest `manifests/problems/heat_kernel_solves_heat_equation.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.HeatKernelWanted` namespace. Mathematical
statements are unchanged. Source: Classical heat-equation theory.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

namespace MathlibExt.Analysis.HeatKernelWanted
namespace Analysis
namespace ODE

/-!
The Gaussian heat kernel solves the 1D heat equation.

Define
  `u(t, x) = (4 π t)^(-1/2) · ∫_ℝ exp(-(x - y)² / (4 t)) · f(y) dy`
for `t > 0`, and extend by `u(t, x) := f x` for `t ≤ 0`. Then on `(0, ∞) × ℝ` we have
  `∂_t u = ∂_x² u`,
and `u(t, x) → f x` as `t ↓ 0` for every `x`.

This is a substantial benchmark because it exercises differentiation under the integral
sign, the explicit Gaussian integral evaluation, approximate-identity arguments for the
initial trace, and the heat-PDE identity satisfied by the kernel itself.

The PDE statement asserts the existence of the spatial first and second derivatives at
each `(t, x)` with `t > 0`, and equates the time derivative of `u` to the spatial second
derivative. Stating things via `HasDerivAt` (rather than relying on `deriv` returning `0`
silently when the derivative does not exist) ensures the Lean statement matches the
intended PDE.
-/

open Real MeasureTheory

/-- The 1D Gaussian heat kernel. Extended by `f x` for `t ≤ 0` so that it is a global
function `ℝ × ℝ → ℝ`; the PDE statement only constrains its behaviour on `t > 0`. -/
noncomputable def heatSolution (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  if 0 < t then
    (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2) *
      ∫ y : ℝ, Real.exp (-((x - y) ^ 2) / (4 * t)) * f y
  else
    f x

/- **The Gaussian heat kernel solves the heat equation.**

For continuous bounded `f : ℝ → ℝ`, the heat-kernel convolution `u := heatSolution f`
satisfies the 1D heat equation `∂_t u = ∂_x² u` on `(0, ∞) × ℝ` (in the sense that the
required spatial derivatives exist and equal the time derivative), and `u(t, x) → f x`
as `t ↓ 0` for every `x`. -/
/-- Source: Classical heat-equation theory. Via leanprover/lean-eval@38361be, problem `heat_kernel_solves_heat_equation`. -/
public theorem_wanted heat_kernel_solves_heat_equation
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) :
    -- The PDE on (0, ∞) × ℝ.
    (∀ t : ℝ, 0 < t → ∀ x : ℝ, ∃ ux : ℝ → ℝ, ∃ uxx : ℝ,
        (∀ y : ℝ, HasDerivAt (fun z => heatSolution f t z) (ux y) y) ∧
        HasDerivAt ux uxx x ∧
        HasDerivAt (fun s => heatSolution f s x) uxx t) ∧
    -- Initial condition recovered as a one-sided limit at t = 0.
    (∀ x : ℝ,
        Filter.Tendsto (fun t : ℝ => heatSolution f t x)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (f x)))

end ODE
end Analysis

end MathlibExt.Analysis.HeatKernelWanted
