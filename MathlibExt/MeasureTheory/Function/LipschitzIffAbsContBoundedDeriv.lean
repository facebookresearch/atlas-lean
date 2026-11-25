/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Lipschitz iff absolutely continuous with a.e. bounded derivative

The following OpenBMB notice applies to the adapted statement and its documentation.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_62.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_62 … := by sorry` into the Batteries `theorem_wanted`
`lipschitzWith_iff_absolutelyContinuous_and_ae_norm_deriv_le`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.LipschitzIffAbsContBoundedDerivWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # Global Lipschitz continuity from a bound on the derivative -/

@[expose] public section

open MeasureTheory Filter

namespace MathlibExt.MeasureTheory.LipschitzIffAbsContBoundedDerivWanted

/-- **Lipschitz functions are the absolutely continuous functions with bounded derivative.** Let
$f : \mathbb{R} \to \mathbb{R}$ and let $M \ge 0$ be a real number. Then
$|f(x) - f(y)| \le M|x - y|$ for all $x, y \in \mathbb{R}$ if and only if $f$ is absolutely
continuous on every closed bounded interval and $|f'(x)| \le M$ for almost every $x \in \mathbb{R}$
(with respect to Lebesgue measure), where $f'(x)$ is taken to be $0$ at points where $f$ is not
differentiable.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_62.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem lipschitzWith_iff_absolutelyContinuous_and_ae_norm_deriv_le
    (f : ℝ → ℝ) (M : NNReal) : (LipschitzWith M f) ↔
  ((∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) ∧ (∀ᵐ x, ‖deriv f x‖ ≤ (M : ℝ))) := by
  constructor
  · intro hf
    exact ⟨fun a b => (hf.lipschitzOnWith (s := Set.uIcc a b)).absolutelyContinuousOnInterval,
      Eventually.of_forall fun _ => norm_deriv_le_of_lipschitz hf⟩
  · rintro ⟨hac, hb⟩
    have hordered {x y : ℝ} (hxy : x ≤ y) : dist (f x) (f y) ≤ (M : ℝ) * dist x y := by
      have hint := (hac x y).intervalIntegrable_deriv
      calc
        dist (f x) (f y) = ‖∫ z in x..y, deriv f z‖ := by
          rw [(hac x y).integral_deriv_eq_sub, dist_comm (f x) (f y), dist_eq_norm]
        _ ≤ ∫ z in x..y, ‖deriv f z‖ := intervalIntegral.norm_integral_le_integral_norm hxy
        _ ≤ ∫ _ in x..y, (M : ℝ) :=
          intervalIntegral.integral_mono_ae hxy hint.norm intervalIntegrable_const hb
        _ = (M : ℝ) * dist x y := by
          rw [intervalIntegral.integral_const, dist_comm x y, Real.dist_eq,
            abs_of_nonneg (sub_nonneg.mpr hxy), smul_eq_mul, mul_comm]
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rcases le_total x y with hxy | hyx
    · exact hordered hxy
    · simpa only [dist_comm (f y) (f x), dist_comm y x] using hordered hyx

end MathlibExt.MeasureTheory.LipschitzIffAbsContBoundedDerivWanted
