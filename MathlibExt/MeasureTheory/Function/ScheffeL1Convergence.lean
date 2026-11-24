/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# A.e. convergence plus convergence of L^1 norms gives L^1 convergence

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_76.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_76 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_integral_abs_sub_of_ae_tendsto_of_tendsto_integral_abs`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.ScheffeL1ConvergenceWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system. The move to this proved module supplies a proof
using the existing measure-space lemma, without changing the ATLAS name or statement.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import MathlibExt.MeasureTheory.Function.ScheffeLemma

/-! # The real-line integral form of Scheffé's lemma -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.ScheffeL1ConvergenceWanted

/-- **Scheffé's lemma on the real line.** Let $f : \mathbb{R} \to \mathbb{R}$ be integrable and
let $(f_n)_{n \in \mathbb{N}}$ be a sequence of integrable real functions $f_n$ on $\mathbb{R}$
such that $f_n(x) \to f(x)$ for almost every $x \in \mathbb{R}$. If
$\int_{\mathbb{R}} |f_n| \to \int_{\mathbb{R}} |f|$ as $n \to \infty$, then
$\int_{\mathbb{R}} |f_n - f| \to 0$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_76.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem tendsto_integral_abs_sub_of_ae_tendsto_of_tendsto_integral_abs
  (f : ℝ → ℝ)
  (fn : ℕ → ℝ → ℝ)
  (hf : MeasureTheory.Integrable f)
  (hfn : ∀ n : ℕ, MeasureTheory.Integrable (fn n))
  (hae : ∀ᵐ x ∂MeasureTheory.volume, Filter.Tendsto (fun n : ℕ => fn n x) Filter.atTop (nhds (f x)))
  (hnorm : Filter.Tendsto
      (fun n : ℕ => ∫ x : ℝ, |fn n x|)
      Filter.atTop
      (nhds (∫ x : ℝ, |f x|))) :
  Filter.Tendsto
    (fun n : ℕ => ∫ x : ℝ, |fn n x - f x|)
    Filter.atTop
    (nhds 0) := by
  have hnorm_eq {g : ℝ → ℝ} (hg : Integrable g) :
      ENNReal.ofReal (∫ x, |g x|) = eLpNorm g 1 volume := by
    rw [eLpNorm_one_eq_lintegral_eNorm hg.aestronglyMeasurable]
    simpa only [Real.norm_eq_abs] using ofReal_integral_norm_eq_lintegral_eNorm hg
  have hnorm_eLp : Tendsto (fun n => eLpNorm (fn n) 1 volume) atTop (𝓝 (eLpNorm f 1 volume)) := by
    simpa only [Function.comp_def, hnorm_eq hf, fun n => hnorm_eq (hfn n)] using
      (ENNReal.continuous_ofReal.tendsto _).comp hnorm
  have hdiff := MeasureTheory.scheffe_lemma (fun n => (hfn n).aestronglyMeasurable)
    (memLp_one_iff_integrable.mpr hf) hae hnorm_eLp
  have heq (n : ℕ) : (∫ x, |fn n x - f x|) = (eLpNorm (fn n - f) 1 volume).toReal := by
    have hm := ((hfn n).sub hf).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_eNorm hm]
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using integral_norm_eq_lintegral_eNorm hm
  simpa only [Function.comp_def, ENNReal.toReal_zero, ← heq] using
    (ENNReal.continuousAt_toReal (x := 0) ENNReal.zero_ne_top).tendsto.comp hdiff

end MathlibExt.MeasureTheory.ScheffeL1ConvergenceWanted
