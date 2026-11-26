/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# A bounded L^1 function on R^d is L^2 with an interpolation bound

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_41.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_41 … := by sorry` into the Batteries `theorem_wanted`
`memLp_two_and_eLpNorm_two_le_of_bounded_of_memLp_one`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.BoundedL1MemL2NormBoundWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
Later changes (ATLAS, 2026): that docstring was restated to match the Lean statement, and the
wanted declaration then moved from
`WantedExt/Analysis/FunctionalAnalysis/BoundedL1MemL2NormBoundWanted.lean` to this module with
its ATLAS name, namespace, statement and docstring unchanged, so the name and the docstring are
ATLAS's, not the benchmark's. The benchmark gives no proof (`by sorry`); this move supplies one
and narrows the imports to the modules used.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The square-integrability bound for bounded integrable functions -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Analysis.FunctionalAnalysis.BoundedL1MemL2NormBoundWanted

/-- **A bounded integrable function is square integrable.** Let $d$ be a natural number, let
$M \ge 0$, and let $f \colon \mathbb{R}^d \to \mathbb{R}$ satisfy $|f(x)| \le M$ for every
$x \in \mathbb{R}^d$. If $f \in L^1(\mathbb{R}^d)$, then $f \in L^2(\mathbb{R}^d)$ and

$$\|f\|_{L^2(\mathbb{R}^d)} \le M^{1/2} \, \|f\|_{L^1(\mathbb{R}^d)}^{1/2},$$

where the spaces and norms are taken with respect to Lebesgue measure.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_41.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem memLp_two_and_eLpNorm_two_le_of_bounded_of_memLp_one
    (d : ℕ) (f : (Fin d → ℝ) → ℝ) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x, ‖f x‖ ≤ M)
    (hf : MeasureTheory.MemLp f 1) :
    (MeasureTheory.MemLp f 2) ∧
      (MeasureTheory.eLpNorm f 2).toReal ≤
        Real.sqrt M * Real.sqrt (MeasureTheory.eLpNorm f 1).toReal := by
  have hmul : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ)) ≤ ENNReal.ofReal M * eLpNorm f 1 := by
    rw [eLpNorm_one_eq_lintegral_eNorm hf.aestronglyMeasurable, ← lintegral_const_mul' _ _
      ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [pow_two]
    have hx : ‖f x‖ₑ ≤ ENNReal.ofReal M := by
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hbound x)
    exact mul_le_mul_of_nonneg_right hx bot_le
  have hfinite : ENNReal.ofReal M * eLpNorm f 1 ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top
  have htwo : eLpNorm f 2 = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by simp) hf.aestronglyMeasurable,
      ENNReal.toReal_ofNat]
    simp only [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  have hLp : eLpNorm f 2 < ∞ := by
    rw [htwo]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
      (ne_of_lt (hmul.trans_lt (lt_top_iff_ne_top.mpr hfinite)))
  refine ⟨hLp, ?_⟩
  rw [htwo, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow]
  calc
    _ ≤ Real.sqrt (ENNReal.ofReal M * eLpNorm f 1).toReal :=
      Real.sqrt_le_sqrt (ENNReal.toReal_mono hfinite hmul)
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM, Real.sqrt_mul hM]

end MathlibExt.Analysis.FunctionalAnalysis.BoundedL1MemL2NormBoundWanted
