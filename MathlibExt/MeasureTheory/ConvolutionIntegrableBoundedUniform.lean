/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Integrable * bounded convolution is uniformly continuous

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_15.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_15 … := by sorry` into the Batteries `theorem_wanted`
`uniformContinuous_convolution_integrable_bounded`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.ConvolutionIntegrableBoundedUniformWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system. The move to this proved module supplies a
proof and narrows the imports, without changing the ATLAS name or statement.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Uniform continuity of integrable–bounded convolution -/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace MathlibExt.MeasureTheory.ConvolutionIntegrableBoundedUniformWanted

/-- **Convolution of an integrable and a bounded function is uniformly continuous.** Let
$d \in \mathbb{N}$, let $f : \mathbb{R}^d \to \mathbb{R}$ be Lebesgue integrable, and let
$g : \mathbb{R}^d \to \mathbb{R}$ be Borel measurable and bounded. Then the convolution
$$
(f * g)(x) = \int_{\mathbb{R}^d} f(x - y)\, g(y)\, dy
$$
is uniformly continuous on $\mathbb{R}^d$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_15.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem uniformContinuous_convolution_integrable_bounded (d : ℕ)
    (f g : (Fin d → ℝ) → ℝ) (hf : MeasureTheory.Integrable f)
    (hg_meas : Measurable g)
    (hg_bdd : Bornology.IsBounded (Set.range g)) :
    UniformContinuous
      (fun x =>
        ∫ y, (f (x - y)) * (g y)) := by
  let X := Fin d → ℝ
  let μ : Measure X := volume
  let L := hf.toL1 f
  let T : C(X × X, X) := ⟨fun w => w.1 + w.2, continuous_fst.add continuous_snd⟩
  have hT (a : X) : MeasurePreserving (T.curry a) μ μ := measurePreserving_add_left μ a
  let S (a : X) := Lp.compMeasurePreserving (T.curry a) (hT a) L
  have hS_cont : Continuous S :=
    (continuous_const : Continuous fun _ : X => L).compMeasurePreservingLp
      T.curry.continuous hT ENNReal.one_ne_top
  have hS_ae (a : X) : (S a : X → ℝ) =ᵐ[μ] fun t => f (a + t) :=
    (Lp.coeFn_compMeasurePreserving L (hT a)).trans
      (hf.coeFn_toL1.comp_tendsto (hT a).quasiMeasurePreserving.tendsto_ae)
  have hnorm (a : X) : ‖S a - L‖ = ∫ t, ‖f (a + t) - f t‖ ∂μ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (S a) L, hS_ae a, hf.coeFn_toL1] with t h₁ h₂ h₃
    change (S a - L) t = S a t - L t at h₁
    rw [h₁, h₂, h₃]
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hg_bdd
  have hg_bound (y : X) : ‖g y‖ ≤ M := hM _ ⟨y, rfl⟩
  have hshift (x : X) : Integrable (fun y => f (x - y)) μ :=
    (μ.measurePreserving_sub_left x).integrable_comp_of_integrable hf
  have hconv (x : X) : Integrable (fun y => f (x - y) * g y) μ :=
    (hshift x).mul_bdd hg_meas.aestronglyMeasurable (Eventually.of_forall hg_bound)
  -- The bound depends only on the displacement, not on the two points.
  let D (a : X) := M * ‖S a - L‖
  have hD : Continuous D := continuous_const.mul (hS_cont.sub continuous_const).norm
  have hD_zero : D 0 = 0 := by simp [D, hnorm, zero_add]
  have hdiff (x z : X) :
      dist (∫ y, f (x - y) * g y ∂μ) (∫ y, f (z - y) * g y ∂μ) ≤ D (x - z) := by
    rw [dist_eq_norm, ← integral_sub (hconv x) (hconv z)]
    calc
      _ ≤ ∫ y, ‖f (x - y) * g y - f (z - y) * g y‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, M * ‖f (x - y) - f (z - y)‖ ∂μ := by
        apply integral_mono (hconv x |>.sub (hconv z) |>.norm)
          ((hshift x |>.sub (hshift z) |>.norm).const_mul M)
        intro y
        change ‖f (x - y) * g y - f (z - y) * g y‖ ≤ M * ‖f (x - y) - f (z - y)‖
        rw [← sub_mul, norm_mul, mul_comm M]
        exact mul_le_mul_of_nonneg_left (hg_bound y) (norm_nonneg _)
      _ = D (x - z) := by
        change _ = M * ‖S (x - z) - L‖
        rw [hnorm, ← integral_const_mul]
        simpa only [sub_add_sub_cancel] using
          (integral_sub_left_eq_self (fun t => M * ‖f (x - z + t) - f t‖) μ z)
  apply Metric.uniformContinuous_iff.mpr
  intro ε hε
  have he : ∀ᶠ a in 𝓝 (0 : X), D a < ε :=
    hD.continuousAt.eventually_lt continuousAt_const (hD_zero ▸ hε)
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ, hδ, fun x z hxz => (hdiff x z).trans_lt (hδ' ?_)⟩
  simpa only [dist_eq_norm, sub_zero] using hxz

end MathlibExt.MeasureTheory.ConvolutionIntegrableBoundedUniformWanted
