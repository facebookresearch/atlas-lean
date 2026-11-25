/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/ODE/LinearStability.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `linear_ode_asymptotic_stability`, rev 1.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (submitter)
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License. lean-eval ships no `NOTICE` file.

The adapted portion is the theorem statement. ATLAS previously namespaced it and converted
it to a wanted declaration, then restated the docstring. This module moves the statement
and docstring intact and supplies the proof.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exponential
import MathlibExt.Analysis.Normed.Algebra.MatrixExponentialIntertwining
import MathlibExt.Analysis.ODE.LinearizedStability

/-!
# Asymptotic stability of linear ODEs

`linear_ode_asymptotic_stability` proves decay to zero for every solution on positive
times by applying the Hurwitz matrix exponential estimate to its value at time one.
-/

public section

open Filter Topology
open scoped Matrix

namespace MathlibExt.Analysis.LinearStabilityWanted.Analysis.ODE

/-- Transport a solution between two positive times by the matrix exponential. -/
private theorem solution_eq_exp_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : ℝ → Fin n → ℝ) (hx : ∀ t, 0 < t → HasDerivAt x (A *ᵥ x t) t)
    {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    x t = NormedSpace.exp ((t - a) • A) *ᵥ x a := by
  let L := LinearMap.toContinuousLinearMap A.toLin'
  let y := fun s : ℝ => (NormedSpace.exp ((t - s) • L)) (x s)
  have hy (s : ℝ) (hs : 0 < s) : HasDerivAt y 0 s := by
    have hL := (hasDerivAt_exp_smul_const L (t - s)).scomp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    have hx' : HasDerivAt x (L (x s)) s := hx s hs
    simpa [y, Function.comp_def, mul_apply_eq_comp] using hL.clm_apply hx'
  have heq := isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun s hs => (hy s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hy s hs).deriv) ht ha
  simpa [y, L, Matrix.exp_to_clm, NormedSpace.exp_zero] using heq

set_option linter.dupNamespace false in
/-- **Asymptotic stability of linear ODEs with eigenvalues in the open left half-plane.** Let
$n \ge 0$ and let $A$ be a real $n \times n$ matrix such that every complex eigenvalue $\mu$ of $A$
(an eigenvalue of $A$ viewed as a complex matrix acting on $\mathbb{C}^n$) satisfies
$\operatorname{Re} \mu < 0$. Let $x : \mathbb{R} \to \mathbb{R}^n$ be a function that, at every
$t > 0$, is differentiable with derivative $x'(t) = A\,x(t)$. Then $\|x(t)\| \to 0$ as
$t \to \infty$, where $\|\cdot\|$ is the sup norm on $\mathbb{R}^n$.

Source: Classical linear stability theory; Hirsch-Smale-Devaney. Via
leanprover/lean-eval@38361be, problem `linear_ode_asymptotic_stability`. -/
theorem linear_ode_asymptotic_stability
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ μ : ℂ,
        Module.End.HasEigenvalue
          (Matrix.toLin' (A.map (algebraMap ℝ ℂ))) μ → μ.re < 0)
    (x : ℝ → (Fin n → ℝ))
    (hx : ∀ t : ℝ, 0 < t → HasDerivAt x (A.mulVec (x t)) t) :
    Filter.Tendsto (fun t : ℝ => ‖x t‖) Filter.atTop (nhds 0) := by
  have hHurwitz : A.IsHurwitz := by
    simpa only [Matrix.IsHurwitz, Module.End.hasEigenvalue_iff_mem_spectrum,
      Matrix.spectrum_toLin'] using hA
  obtain ⟨M, α, _, hα, hbound⟩ := hHurwitz.exists_norm_exp_smul_mulVec_le
  have hshift : Tendsto (fun t : ℝ => t - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id
  have hdecay : Tendsto (fun t : ℝ => Real.exp (-(α * (t - 1)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hshift.const_mul_atTop hα)
  have hlim := (hdecay.const_mul M).mul_const ‖x 1‖
  apply squeeze_zero' (.of_forall fun _ => norm_nonneg _) _ (by simpa using hlim)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  rw [solution_eq_exp_mulVec A x hx zero_lt_one (zero_lt_one.trans_le ht)]
  exact hbound (t - 1) (sub_nonneg.mpr ht) (x 1)

end MathlibExt.Analysis.LinearStabilityWanted.Analysis.ODE
