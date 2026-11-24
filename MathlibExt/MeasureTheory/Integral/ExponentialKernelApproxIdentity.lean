/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# n∬f(x)f(y)e^{−2n|x−y|} → ∫f² for f ∈ L²

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_96.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_96 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_mul_integral_integral_exp_neg_two_mul_abs_sub`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.ExponentialKernelApproxIdentityWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-! # An exponential approximate identity in Lebesgue L² -/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace

namespace MathlibExt.MeasureTheory.ExponentialKernelApproxIdentityWanted

private noncomputable def K (t : ℝ) : ℝ := Real.exp (-2 * |t|)

private theorem K_nonneg (t : ℝ) : 0 ≤ K t := (Real.exp_pos _).le

private theorem K_continuous : Continuous K := by unfold K; fun_prop

private theorem K_integrable : Integrable K volume := by
  have hleft : IntegrableOn K (Iic 0) volume :=
    (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 2) 0).congr_fun
      (fun t ht => by simp [K, abs_of_nonpos (mem_Iic.mp ht)]) measurableSet_Iic
  have hright : IntegrableOn K (Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).congr_fun
      (fun t ht => by simp [K, abs_of_pos (mem_Ioi.mp ht)]) measurableSet_Ioi
  simpa only [Iic_union_Ioi, integrableOn_univ] using hleft.union hright

private theorem integral_K : ∫ t, K t = 1 := by
  have hleft : (∫ t in Iic (0 : ℝ), K t) = ∫ t in Iic (0 : ℝ), Real.exp (2 * t) := by
    apply setIntegral_congr_fun measurableSet_Iic
    intro t ht
    simp [K, abs_of_nonpos (mem_Iic.mp ht)]
  have hright : (∫ t in Ioi (0 : ℝ), K t) = ∫ t in Ioi (0 : ℝ), Real.exp (-2 * t) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp [K, abs_of_pos (mem_Ioi.mp ht)]
  rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic K_integrable, compl_Iic,
    hleft, hright, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 2),
    integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)]
  norm_num

/-- **Exponential kernel approximate identity.** For every function $f : \mathbb{R} \to \mathbb{R}$
in $L^2(\mathbb{R})$,
$$
\lim_{n\to\infty} n\int_{\mathbb{R}}\int_{\mathbb{R}} f(x)f(y)e^{-2n|x-y|}\,dy\,dx
= \int_{\mathbb{R}} f(x)^2\,dx,
$$
where $n$ runs through the natural numbers and the integrals are with respect to Lebesgue measure.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_96.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem tendsto_mul_integral_integral_exp_neg_two_mul_abs_sub
    (f : ℝ → ℝ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume) :
    Filter.Tendsto
      (fun n : ℕ =>
        (n : ℝ) * (∫ x : ℝ, ∫ y : ℝ, f x * f y * Real.exp (-2 * (n : ℝ) * |x - y|)))
      Filter.atTop
      (nhds (∫ x : ℝ, f x ^ (2 : ℕ))) := by
  let μ : Measure ℝ := volume
  let L := hf.toLp f
  have hLf : (L : ℝ → ℝ) =ᵐ[μ] f := hf.coeFn_toLp
  have hLm : Measurable (L : ℝ → ℝ) := Lp.stronglyMeasurable L |>.measurable
  let T : C(ℝ × ℝ, ℝ) := ⟨fun z => z.2 - z.1, continuous_snd.sub continuous_fst⟩
  have hT (a : ℝ) : MeasurePreserving (T.curry a) μ μ := measurePreserving_sub_right μ a
  let S (a : ℝ) := Lp.compMeasurePreserving (T.curry a) (hT a) L
  have hS : Continuous S := (continuous_const : Continuous fun _ : ℝ => L).compMeasurePreservingLp
    T.curry.continuous hT (by norm_num)
  let C (a : ℝ) := ∫ x, L x * L (x - a) ∂μ
  have hCinner (a : ℝ) : C a = inner ℝ L (S a) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving L (hT a)] with x hx
    change S a x = L (x - a) at hx
    simp [RCLike.inner_apply, hx, mul_comm]
  have hC : Continuous C := by
    rw [show C = fun a => inner ℝ L (S a) from funext hCinner]
    exact continuous_const.inner hS
  let B := ∫ x, L x ^ (2 : ℕ) ∂μ
  have hCzero : C 0 = B := by simp [C, B, pow_two]
  have hsq : Integrable (fun x => L x ^ (2 : ℕ)) μ :=
    (memLp_two_iff_integrable_sq hLm.aestronglyMeasurable).mp (Lp.memLp L)
  have hpair (a : ℝ) : Integrable (fun x => L x * L (x - a)) μ :=
    (Lp.memLp L).integrable_mul ((Lp.memLp L).comp_measurePreserving (hT a))
  have hpair_bound (a : ℝ) : (∫ x, ‖L x * L (x - a)‖ ∂μ) ≤ B := by
    have hshift : Integrable (fun x => L (x - a) ^ (2 : ℕ)) μ :=
      (hT a).integrable_comp_of_integrable hsq
    calc
      _ ≤ ∫ x, (1 / 2 : ℝ) * (L x ^ (2 : ℕ) + L (x - a) ^ (2 : ℕ)) ∂μ := by
        apply integral_mono (hpair a).norm ((hsq.add hshift).const_mul (1 / 2 : ℝ))
        intro x
        change ‖L x * L (x - a)‖ ≤ (1 / 2 : ℝ) * (L x ^ (2 : ℕ) + L (x - a) ^ (2 : ℕ))
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · nlinarith [sq_nonneg (L x + L (x - a))]
        · nlinarith [sq_nonneg (L x - L (x - a))]
      _ = B := by
        rw [integral_const_mul, integral_add hsq hshift,
          integral_sub_right_eq_self (fun x => L x ^ (2 : ℕ)) a]
        change (1 / 2 : ℝ) * (B + B) = B
        ring
  have hC_bd (a : ℝ) : ‖C a‖ ≤ B := (norm_integral_le_integral_norm _).trans (hpair_bound a)
  -- After scaling the displacement, the same kernel is used for all indices.
  let H (n : ℕ) (t x : ℝ) := K t * (L x * L (x - t / (n : ℝ)))
  have hH_int (n : ℕ) : Integrable (Function.uncurry (H n)) (μ.prod μ) := by
    have hHm : Measurable (Function.uncurry (H n)) := by
      unfold Function.uncurry H
      exact (K_continuous.measurable.comp measurable_fst).mul ((hLm.comp measurable_snd).mul
        (hLm.comp (measurable_snd.sub (measurable_fst.div measurable_const))))
    apply (integrable_prod_iff hHm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall fun t => (hpair (t / (n : ℝ))).const_mul (K t), ?_⟩
    apply (K_integrable.mul_const B).mono' hHm.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards with t
    change ‖∫ x, ‖H n t x‖ ∂μ‖ ≤ K t * B
    have hnonneg : 0 ≤ ∫ x, ‖H n t x‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    change (∫ x, ‖K t * (L x * L (x - t / (n : ℝ)))‖ ∂μ) ≤ K t * B
    simp only [norm_mul (K t), Real.norm_of_nonneg (K_nonneg t), integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hpair_bound _) (K_nonneg t)
  have hinner (n : ℕ) (hn : 0 < n) (x : ℝ) :
      (∫ y, L x * L y * Real.exp (-2 * (n : ℝ) * |x - y|) ∂μ) =
        (n : ℝ)⁻¹ * ∫ t, H n t x ∂μ := by
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    calc
      _ = ∫ u, L x * L (x - u) * Real.exp (-2 * (n : ℝ) * |u|) ∂μ := by
        convert integral_sub_left_eq_self
          (fun u => L x * L (x - u) * Real.exp (-2 * (n : ℝ) * |u|)) μ x using 2
        simp
      _ = ∫ u, H n ((n : ℝ) * u) x ∂μ := by
        apply integral_congr_ae
        filter_upwards with u
        have hcancel : (n : ℝ) * u / (n : ℝ) = u := by field_simp
        unfold H K
        rw [hcancel, abs_mul, abs_of_pos hn']
        ring_nf
      _ = _ := by
        simpa only [abs_of_pos (inv_pos.mpr hn'), smul_eq_mul] using
          Measure.integral_comp_mul_left (fun t => H n t x) (n : ℝ)
  have hrewrite (n : ℕ) (hn : 0 < n) :
      (n : ℝ) * (∫ x, ∫ y, L x * L y * Real.exp (-2 * (n : ℝ) * |x - y|) ∂μ ∂μ) =
        ∫ t, K t * C (t / (n : ℝ)) ∂μ := by
    have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
    simp only [hinner n hn, integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hn', one_mul]
    rw [← integral_integral_swap (hH_int n)]
    simp only [H, C, integral_const_mul]
  have hlim : Tendsto (fun n : ℕ => ∫ t, K t * C (t / (n : ℝ)) ∂μ) atTop (𝓝 B) := by
    have hD := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := fun (n : ℕ) (t : ℝ) => K t * C (t / (n : ℝ)))
      (f := fun t => K t * B) (fun t => K t * B)
      (fun n => (K_continuous.mul (hC.comp (continuous_id.div_const _))).aestronglyMeasurable)
      (K_integrable.mul_const B)
      (fun n => Eventually.of_forall fun t => by
        rw [norm_mul, Real.norm_of_nonneg (K_nonneg t)]
        exact mul_le_mul_of_nonneg_left (hC_bd _) (K_nonneg t))
      (Eventually.of_forall fun t => by
        have ht : Tendsto (fun n : ℕ => t / (n : ℝ)) atTop (𝓝 0) := by
          simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
            tendsto_const_nhds.mul ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
              tendsto_natCast_atTop_atTop)
        simpa only [hCzero, Function.comp_apply] using
          tendsto_const_nhds.mul (hC.continuousAt.tendsto.comp ht))
    have hK : (∫ t, K t ∂μ) = 1 := integral_K
    simpa only [integral_mul_const, hK, one_mul] using hD
  have hB : B = ∫ x, f x ^ (2 : ℕ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hLf] with x hx
    rw [hx]
  rw [hB] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [← hrewrite n hn]
  congr 1
  apply integral_congr_ae
  filter_upwards [hLf] with x hx
  apply integral_congr_ae
  filter_upwards [hLf] with y hy
  rw [hx, hy]

end MathlibExt.MeasureTheory.ExponentialKernelApproxIdentityWanted
