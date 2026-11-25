/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Bounded a.e.-null sequences in L^p converge weakly to 0

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_10.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_10 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_integral_mul_of_ae_tendsto_zero_of_eLpNorm_le_one`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.FunctionalAnalysis.WeakConvergenceOfBoundedAeNullLpWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Tactic.FunProp

/-! # Weak convergence of bounded almost-everywhere-null sequences in Lp -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MathlibExt.Analysis.FunctionalAnalysis.WeakConvergenceOfBoundedAeNullLpWanted

/-- **Lebesgue measure on $(0,1)$.** The measure on $\mathbb{R}$ obtained by restricting
Lebesgue measure to the open interval $(0, 1)$. -/
noncomputable abbrev μI01 : Measure ℝ := Measure.restrict volume (Set.Ioo (0 : ℝ) 1)

/-- **Bounded a.e.-null sequences in $L^p(0,1)$ converge weakly to zero.** Let $1 < p < \infty$
and let $q$ be the conjugate exponent, so that $1/p + 1/q = 1$. Write $L^p(0,1)$ and $L^q(0,1)$
for the Lebesgue spaces of real functions on $(0,1)$ with Lebesgue measure. Let
$(f_n)_{n \in \mathbb{N}}$ be a sequence in $L^p(0,1)$ with $\|f_n\|_{L^p} \le 1$ for every $n$
and $f_n(x) \to 0$ for almost every $x \in (0,1)$. Then for every $g \in L^q(0,1)$,
$$
\int_0^1 f_n(x)\, g(x)\, dx \to 0 \quad (n \to \infty).
$$

Since $L^q(0,1)$ is the dual of $L^p(0,1)$, this says that $(f_n)$ converges weakly to $0$ in
$L^p(0,1)$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Normed
linear spaces and Banach spaces; Banach lattices), `benchmark/level2/ma_proofbench_l2_10.lean`
at openbmb/ma-proofbench@31bab4c.
-/
theorem tendsto_integral_mul_of_ae_tendsto_zero_of_eLpNorm_le_one
    (p q : ENNReal)
    (hp_ne_top : p ≠ ⊤)
    (hp_gt_one : 1 < p)
    (hq : 1 / p + 1 / q = 1)
    (f : ℕ → Lp ℝ p μI01)
    (h_bound : ∀ n, eLpNorm (f n) p μI01 ≤ 1)
    (h_ae : ∀ᵐ x ∂μI01, Tendsto (fun n => f n x) atTop (nhds 0)) :
    ∀ g : Lp ℝ q μI01, Tendsto (fun n => ∫ x, (f n x) * g x ∂μI01) atTop (nhds 0) := by
  intro g
  let : p.HolderConjugate q := ENNReal.holderConjugate_iff.mpr (by simpa only [one_div] using hq)
  have hq_one : 1 ≤ q := (ENNReal.HolderConjugate.lt_top_iff_one_lt p q).mp hp_ne_top.lt_top |>.le
  have hq_fin : q ≠ ∞ := ((ENNReal.HolderConjugate.lt_top_iff_one_lt q p).mpr hp_gt_one).ne
  let : IsFiniteMeasure μI01 := ⟨by rw [μI01, Measure.restrict_apply_univ, Real.volume_Ioo]; simp⟩
  let F (n : ℕ) (x : ℝ) := f n x * g x
  have hmeas_f (n : ℕ) : AEStronglyMeasurable (f n : ℝ → ℝ) μI01 :=
    (Lp.memLp (f n)).aestronglyMeasurable
  have hmeas_g : AEStronglyMeasurable (g : ℝ → ℝ) μI01 := (Lp.memLp g).aestronglyMeasurable
  have hF (n : ℕ) : AEStronglyMeasurable (F n) μI01 := (hmeas_f n).mul hmeas_g
  -- The fixed test function has small Lq norm on all sufficiently small sets. The common
  -- Lp bound and Hölder's inequality transfer this control to the products in L¹.
  have hUI : UnifIntegrable F 1 μI01 := by
    refine unifIntegrable_iff'.mpr fun ε hε => ?_
    obtain ⟨δ, hδ, hg⟩ := (Lp.memLp g).eLpNorm_indicator_le hq_one hq_fin hε
    refine ⟨δ, hδ, fun n s hs hμ => ?_⟩
    have hn : eLpNorm (f n) p (μI01.restrict s) ≤ 1 :=
      (eLpNorm_restrict_le (f n : ℝ → ℝ) p μI01 s).trans (h_bound n)
    have hgs : eLpNorm g q (μI01.restrict s) ≤ ε := by
      rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
      exact hg s hs.nullMeasurableSet hμ
    have hprod : eLpNorm (F n) 1 (μI01.restrict s) ≤
        eLpNorm (f n) p (μI01.restrict s) * eLpNorm g q (μI01.restrict s) := by
      simpa only [ENNReal.coe_one, one_mul] using
        (eLpNorm_le_eLpNorm_mul_eLpNorm (μ := μI01.restrict s) (p := p) (q := q) (r := 1)
          (fun a b : ℝ => a * b) 1 (by fun_prop) (hmeas_f n).restrict
          hmeas_g.restrict (.of_forall fun x => by rw [nnNorm_mul, one_mul]))
    exact hprod.trans ((mul_le_mul' hn hgs).trans_eq (one_mul ε))
  have hF_lim : ∀ᵐ x ∂μI01, Tendsto (fun n => F n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [h_ae] with x hx
    simpa only [F, zero_mul] using hx.mul_const (g x)
  have hLp : Tendsto (fun n => eLpNorm (F n) 1 μI01) atTop (𝓝 0) := by
    simpa only [sub_zero] using tendsto_Lp_finite_of_tendsto_ae le_rfl ENNReal.one_ne_top
      hF (MemLp.zero (p := 1) (μ := μI01) (ε := ℝ)) hUI hF_lim
  have hReal : Tendsto (fun n => (eLpNorm (F n) 1 μI01).toReal) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.continuousAt_toReal ENNReal.zero_ne_top).tendsto.comp hLp
  refine tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) ?_ hReal)
  intro n
  calc
    ‖∫ x, F n x ∂μI01‖ ≤ ∫ x, ‖F n x‖ ∂μI01 := norm_integral_le_integral_norm _
    _ = (eLpNorm (F n) 1 μI01).toReal := by
      rw [integral_norm_eq_lintegral_eNorm (hF n), eLpNorm_one_eq_lintegral_eNorm (hF n)]

end MathlibExt.Analysis.FunctionalAnalysis.WeakConvergenceOfBoundedAeNullLpWanted
