/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Large deviations of mean-zero sums on the cube have vanishing measure

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_06.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l2_06 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_volume_abs_sum_ge_mul_sqrt`; moved the informal problem statement docstring onto it and
placed the declarations in namespace
`MathlibExt.MeasureTheory.MeanZeroSumDeviationMeasureWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Chebyshev's inequality for coordinate sums on a cube -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal Topology

namespace MathlibExt.MeasureTheory.MeanZeroSumDeviationMeasureWanted

/-- **Large deviations of mean-zero sums on the cube have vanishing measure.** Let
$f : \mathbb{R} \to \mathbb{R}$ be square integrable on $[0,1]$ with $\int_0^1 f = 0$ and
$\int_0^1 |f|^2 > 0$, and let $(a_n)_{n \in \mathbb{N}}$ be a sequence of positive reals with
$a_n \to \infty$. For each $n$ let
$$F_n = \{ (x_1, \dots, x_n) \in [0,1]^n : |f(x_1) + \cdots + f(x_n)| \ge a_n \sqrt{n} \}.$$
Then $m_n(F_n) \to 0$ as $n \to \infty$, where $m_n$ is Lebesgue measure on $\mathbb{R}^n$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_06.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem tendsto_volume_abs_sum_ge_mul_sqrt (f : ℝ → ℝ) (a : ℕ → ℝ)
    (hf_L2 : MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hf_mean_zero : ∫ x, f x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0)
    (hf_sq_pos : 0 < ∫ x, |f x| ^ 2 ∂(volume.restrict (Set.Icc (0 : ℝ) 1)))
    (ha_pos : ∀ n, 0 < a n)
    (ha_tendsto : Filter.Tendsto a Filter.atTop Filter.atTop)
    (F : ∀ n : ℕ, Set (Fin n → ℝ))
    (hF : ∀ n x, x ∈ F n ↔
      (∀ i : Fin n, x i ∈ Set.Icc (0 : ℝ) 1) ∧
      a n * Real.sqrt n ≤ |∑ i : Fin n, f (x i)|) :
    Filter.Tendsto (fun n => volume (F n)) Filter.atTop (nhds 0) := by
  let μ : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  let P (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => μ)
  let X (n : ℕ) (i : Fin n) (x : Fin n → ℝ) := f (x i)
  let S (n : ℕ) : (Fin n → ℝ) → ℝ := ∑ i, X n i
  let σsq := ∫ x, |f x| ^ (2 : ℕ) ∂μ
  have hvar : variance f μ = σsq := by
    rw [variance_eq_integral hf_L2.aemeasurable]
    change (∫ x, (f x - ∫ y, f y ∂μ) ^ (2 : ℕ) ∂μ) = σsq
    have hm : (∫ y, f y ∂μ) = 0 := hf_mean_zero
    simp only [hm, sub_zero, σsq, sq_abs]
  have hS_apply (n : ℕ) (x : Fin n → ℝ) : S n x = ∑ i, f (x i) :=
    Finset.sum_apply _ _ _
  have hX (n : ℕ) (i : Fin n) : MemLp (X n i) 2 (P n) :=
    hf_L2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i)
  have hS (n : ℕ) : MemLp (S n) 2 (P n) := by
    rw [show S n = (fun x => ∑ i, f (x i)) from funext (hS_apply n)]
    exact memLp_finsetSum Finset.univ (f := X n) fun i _ => hX n i
  have hEX (n : ℕ) (i : Fin n) : (∫ x, X n i x ∂P n) = 0 := by
    have h := measurePreserving_eval (fun _ : Fin n => μ) i
    have hm : AEStronglyMeasurable f (Measure.map (Function.eval i) (P n)) := by
      rw [h.map_eq]
      exact hf_L2.aestronglyMeasurable
    change (∫ x, f (Function.eval i x) ∂P n) = 0
    rw [← integral_map h.measurable.aemeasurable hm, h.map_eq]
    exact hf_mean_zero
  have hES (n : ℕ) : (∫ x, S n x ∂P n) = 0 := by
    simp_rw [hS_apply]
    change (∫ x, ∑ i, X n i x ∂P n) = 0
    rw [integral_finsetSum _ fun i _ => (hX n i).integrable one_le_two]
    simp only [hEX, Finset.sum_const_zero]
  have hVS (n : ℕ) : variance (S n) (P n) = (n : ℝ) * σsq := by
    have h := variance_sum_pi (ι := Fin n) (μ := fun _ => μ) (X := fun _ => f) (fun _ => hf_L2)
    simpa [S, P, X, hvar, nsmul_eq_mul] using h
  -- Product probability on the cube is its restricted Lebesgue measure.
  have hP (n : ℕ) : P n = (volume : Measure (Fin n → ℝ)).restrict
      (univ.pi fun _ : Fin n => Icc (0 : ℝ) 1) := by
    change Measure.pi (fun _ : Fin n => volume.restrict (Icc (0 : ℝ) 1)) = _
    rw [← Measure.restrict_pi_pi, ← volume_pi]
  have hevent (n : ℕ) : (P n) {x | a n * Real.sqrt n ≤ |S n x|} = volume (F n) := by
    rw [hP, Measure.restrict_apply' (MeasurableSet.univ_pi fun _ => measurableSet_Icc)]
    congr 1
    ext x
    simpa only [mem_inter_iff, mem_ofPred_eq, mem_univ_pi, hS_apply, and_comm] using (hF n x).symm
  have hbound {n : ℕ} (hn : 0 < n) : volume (F n) ≤ ENNReal.ofReal (σsq / a n ^ 2) := by
    have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have h := meas_ge_le_variance_div_sq (hS n) (mul_pos (ha_pos n) (Real.sqrt_pos.2 hn'))
    rw [hES n, hVS n] at h
    simp only [sub_zero] at h
    rw [hevent n, mul_pow, Real.sq_sqrt hn'.le] at h
    have hcancel : (n : ℝ) * σsq / (a n ^ 2 * (n : ℝ)) = σsq / a n ^ 2 := by
      field_simp [hn'.ne', (ha_pos n).ne']
    rwa [hcancel] at h
  have hInv2 : Tendsto (fun n => (a n ^ 2)⁻¹) atTop (𝓝 0) := by
    have hInv := (tendsto_inv_atTop_zero (𝕜 := ℝ)).comp ha_tendsto
    simpa only [inv_pow, zero_pow two_ne_zero, Function.comp_apply] using hInv.pow 2
  have hlimit : Tendsto (fun n => ENNReal.ofReal (σsq / a n ^ 2)) atTop (𝓝 0) := by
    have hσsq : 0 ≤ σsq := hf_sq_pos.le
    simp_rw [div_eq_mul_inv, ENNReal.ofReal_mul hσsq]
    simpa only [ENNReal.ofReal_zero, mul_zero] using
      ENNReal.Tendsto.const_mul (a := ENNReal.ofReal σsq) (ENNReal.tendsto_ofReal hInv2)
        (Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact hbound hn

end MathlibExt.MeasureTheory.MeanZeroSumDeviationMeasureWanted
