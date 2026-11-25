/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# ∫||f|^p − |g|^p| ≤ ∫|f − g|^p for 0 < p < 1

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_53.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_53 … := by sorry` into the Batteries `theorem_wanted`
`integral_abs_rpow_sub_rpow_le_integral_rpow_abs_sub`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.LpSubadditivePowLtOneWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system. The move to this proved module supplies a proof and
narrows the imports, without changing the ATLAS name or statement.
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.MeanInequalitiesPow

/-! # An integral inequality for powers below one -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.MeasureTheory.LpSubadditivePowLtOneWanted

/-- **An integral inequality for $p$-th powers with $0 < p < 1$.** Let $\mu$ be a measure on a
measurable space and let $0 < p < 1$. Then for all real-valued $f, g \in L^p(\mu)$,
$$\int \bigl||f|^p - |g|^p\bigr|\,d\mu \le \int |f - g|^p\,d\mu.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_53.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem integral_abs_rpow_sub_rpow_le_integral_rpow_abs_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ENNReal} (hp0 : 0 < p) (hp1 : p < 1)
    {f g : Lp ℝ p μ} :
    (∫ x, |((|f x|) ^ p.toReal) - ((|g x|) ^ p.toReal)| ∂μ) ≤
      ∫ x, (|f x - g x|) ^ p.toReal ∂μ := by
  have hp_ne_top : p ≠ ∞ := (hp1.trans ENNReal.one_lt_top).ne
  have hq1 : p.toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top hp1.le
  have hf : Integrable (fun x => |f x| ^ p.toReal) μ := by
    simpa only [Real.norm_eq_abs] using (Lp.memLp f).integrable_norm_rpow hp0.ne' hp_ne_top
  have hg : Integrable (fun x => |g x| ^ p.toReal) μ := by
    simpa only [Real.norm_eq_abs] using (Lp.memLp g).integrable_norm_rpow hp0.ne' hp_ne_top
  have hleft : Integrable (fun x => abs (|f x| ^ p.toReal - |g x| ^ p.toReal)) μ := by
    simpa only [Pi.sub_apply] using (hf.sub hg).abs
  have hright : Integrable (fun x => |f x - g x| ^ p.toReal) μ := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      ((Lp.memLp f).sub (Lp.memLp g)).integrable_norm_rpow hp0.ne' hp_ne_top
  have hdiff (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      a ^ p.toReal - b ^ p.toReal ≤ |a - b| ^ p.toReal := by
    have hab : a ≤ b + |a - b| := sub_le_iff_le_add'.mp (le_abs_self (a - b))
    exact sub_le_iff_le_add'.mpr <|
      (Real.rpow_le_rpow ha hab ENNReal.toReal_nonneg).trans
        (Real.rpow_add_le_add_rpow hb (abs_nonneg _) ENNReal.toReal_nonneg hq1)
  apply integral_mono hleft hright
  intro x
  have hbnd : abs (|f x| ^ p.toReal - |g x| ^ p.toReal) ≤ abs (|f x| - |g x|) ^ p.toReal := by
    refine abs_sub_le_iff.mpr ⟨hdiff _ _ (abs_nonneg _) (abs_nonneg _), ?_⟩
    rw [abs_sub_comm]
    exact hdiff _ _ (abs_nonneg _) (abs_nonneg _)
  exact hbnd.trans <| Real.rpow_le_rpow (abs_nonneg _)
    (abs_abs_sub_abs_le_abs_sub _ _) ENNReal.toReal_nonneg

end MathlibExt.MeasureTheory.LpSubadditivePowLtOneWanted
