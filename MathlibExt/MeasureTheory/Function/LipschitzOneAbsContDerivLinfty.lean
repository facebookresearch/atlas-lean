/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# A 1-Lipschitz function on [a,b] is absolutely continuous with f' in L^∞

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_34.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_34 … := by sorry` into the Batteries `theorem_wanted`
`absolutelyContinuousOnInterval_and_eLpNorm_deriv_lt_top_of_lipschitzOnWith`; moved the informal
problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.LipschitzOneAbsContDerivLinftyWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Absolute continuity and a bounded derivative for interval Lipschitz functions -/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.LipschitzOneAbsContDerivLinftyWanted

/-- **A $1$-Lipschitz function on $[a,b]$ is absolutely continuous with essentially bounded
derivative.** Let $a \le b$ be real numbers and let $f : \mathbb{R} \to \mathbb{R}$ satisfy
$|f(x) - f(y)| \le |x - y|$ for all $x, y \in [a, b]$. Then $f$ is absolutely continuous on
$[a, b]$, and its derivative $f'$, taken to be $0$ at points where $f$ is not differentiable, has
finite norm $\|f'\|_{L^\infty[a,b]}$, the essential supremum with respect to Lebesgue measure on
$[a, b]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_34.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem absolutelyContinuousOnInterval_and_eLpNorm_deriv_lt_top_of_lipschitzOnWith
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : LipschitzOnWith 1 f (Set.Icc a b)) :
    AbsolutelyContinuousOnInterval f a b ∧
      eLpNorm (fun x => deriv f x) ⊤ (volume.restrict (Set.Icc a b)) < ⊤ := by
  have hu : LipschitzOnWith 1 f (uIcc a b) := by rwa [uIcc_of_le hab]
  refine ⟨hu.absolutelyContinuousOnInterval, ?_⟩
  rw [eLpNorm_exponent_top (aestronglyMeasurable_deriv f _)]
  refine (eLpNormEssSup_le_of_ae_eNorm_bound (C := 1) ?_).trans_lt ENNReal.one_lt_top
  -- The derivative bound uses a neighborhood in the interval. Removing its endpoints
  -- leaves the restricted measure unchanged, also when the interval degenerates to a point.
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := a) (b := b))]
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with x hx
  have hd : ‖deriv f x‖ ≤ 1 := by
    simpa using norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hx.1 hx.2) hf
  rw [← ofReal_norm, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal hd

end MathlibExt.MeasureTheory.LipschitzOneAbsContDerivLinftyWanted
