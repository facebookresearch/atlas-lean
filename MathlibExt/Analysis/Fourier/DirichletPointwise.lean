/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/FourierConvergence.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `fourier_dirichlet_fejer`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/fourier_dirichlet_fejer.toml`, rev 1): the statement of
`dirichlet_pointwise` and its docstring.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). ATLAS first converted the benchmark
statement to a wanted declaration under its current namespace. This module moves the statement
from `WantedExt/Analysis/FourierConvergenceWanted.lean` and supplies its proof.
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import MathlibExt.Analysis.Fourier.Fejer

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# Dirichlet's pointwise convergence theorem for C¹ functions

`dirichlet_pointwise` proves convergence of the symmetric Fourier partial sums of a
continuously differentiable, `2π`-periodic complex function at every real point. The proof
uses absolute convergence on the circle and restricts the finite sums to symmetric intervals.
-/

@[expose] public section

namespace MathlibExt.Analysis.FourierConvergenceWanted
namespace Analysis

open Filter Topology
open Fourier.AddCircle.C1FourierSummable

set_option linter.dupNamespace false in
/- **Dirichlet's pointwise convergence theorem** (§46). For every `C¹`
2π-periodic complex function `f`, the symmetric Fourier partial sums `S_N(f)(x)`
converge to `f(x)` at every point `x ∈ ℝ`. -/
/-- **Dirichlet's theorem on pointwise convergence of Fourier series.** Let
$f \colon \mathbb{R} \to \mathbb{C}$ be $2\pi$-periodic and continuously differentiable, and for
$n \in \mathbb{Z}$ let $\hat f_n = \frac{1}{2\pi} \int_0^{2\pi} e^{-int} f(t)\,dt$ be the $n$-th
Fourier coefficient of $f$ on $[0, 2\pi]$. Then for every $x \in \mathbb{R}$ the symmetric Fourier
partial sums $S_N(f)(x) = \sum_{n=-N}^{N} \hat f_n e^{inx}$ converge to $f(x)$ as $N \to \infty$.

Source: P. G. L. Dirichlet (1829) and L. Fejér (1900). Listed as §46 in O. Knill, Some Fundamental
Theorems in Mathematics
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `fourier_dirichlet_fejer`. -/
theorem dirichlet_pointwise
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hC1 : ContDiff ℝ 1 f)
    (x : ℝ) :
    Tendsto (fun N : ℕ => fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have hcont := _hC1.continuous
  have hSum := hasSum_fourier_series_of_hasDerivAt Real.two_pi_pos _hperiod hcont
    (fun t => (_hC1.differentiable_one t).hasDerivAt) _hC1.continuous_deriv_one
  have hPointwise := (ContinuousMap.evalCLM ℂ (x : AddCircle (2 * Real.pi))).hasSum hSum
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply,
    liftPeriodicContinuousMap_coe_two_pi _hperiod hcont x] at hPointwise
  have hPartial := hPointwise.comp (Finset.tendsto_Icc_neg (R := ℤ))
  simpa only [Function.comp_def, fourierPartialSum_eq_partialFourierSum _hperiod hcont,
    AddCircle.partialFourierSum, fourierCoeff_liftPeriodicContinuousMap Real.two_pi_pos]
    using hPartial

end Analysis

end MathlibExt.Analysis.FourierConvergenceWanted
