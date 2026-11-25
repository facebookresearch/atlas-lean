/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file (the statement and its docstring) are adapted from MA-ProofBench:
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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_95.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. The statement was renamed to
`tendsto_integral_abs_sum_cube_div_sqrt` in namespace
`MathlibExt.MeasureTheory.CubeAbsSumIntegralAsymptoticWanted`, with the informal problem statement
moved onto it as a docstring. The proof below is original to ATLAS.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.InfinitePi
import MathlibExt.Probability.Distributions.Uniform
import MathlibExt.Probability.Martingale.BipowerVariation

/-!
# Mean absolute sum on the unit cube

On a countable product of unit intervals the normalized coordinate sums converge in law to
`N(0, 1/12)`. Truncating the absolute value and using a common second-moment bound upgrades
convergence in law to convergence of the absolute first moments.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MathlibExt.MeasureTheory.CubeAbsSumIntegralAsymptoticWanted

noncomputable section

/-- Truncating the absolute value at `R` loses at most the second moment divided by `R`. -/
private lemma abs_truncation_error {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ} (hY : MemLp Y 2 P) {R : ℝ} (hR : 0 < R) :
    dist (∫ x, |Y x| ∂P) (∫ x, min |Y x| R ∂P) ≤ (∫ x, (Y x) ^ 2 ∂P) / R := by
  have ha : Integrable (fun x ↦ |Y x|) P := (hY.integrable (by simp)).abs
  have ht : Integrable (fun x ↦ min |Y x| R) P := by
    have hm : Continuous (fun t : ℝ ↦ min |t| R) := continuous_abs.min continuous_const
    refine (integrable_const R).mono'
      (hm.measurable.comp_aemeasurable hY.aemeasurable).aestronglyMeasurable ?_
    exact ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) hR.le)]
      exact min_le_right ..
  have hp (x : Ω) : 0 ≤ |Y x| - min |Y x| R := sub_nonneg.mpr (min_le_left ..)
  rw [Real.dist_eq, ← integral_sub ha ht, abs_of_nonneg (integral_nonneg hp), ← integral_div]
  refine integral_mono (ha.sub ht) (hY.integrable_sq.div_const R) fun x ↦ ?_
  by_cases hx : |Y x| ≤ R
  · rw [min_eq_left hx, sub_self]
    positivity
  · have hy : R ≤ |Y x| := le_of_not_ge hx
    rw [min_eq_right hy, le_div_iff₀ hR, ← sq_abs]
    nlinarith [mul_nonneg hR.le (abs_nonneg (Y x)),
      mul_le_mul_of_nonneg_right hy (abs_nonneg (Y x))]

/-- With a common second-moment bound, weak convergence implies convergence of absolute means. -/
private lemma tendsto_integral_abs_of_secondMoment_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ} {C : ℝ}
    (h : TendstoInDistribution X atTop Y (fun _ ↦ P) Q)
    (hX : ∀ n, MemLp (X n) 2 P) (hY : MemLp Y 2 Q)
    (hX₂ : ∀ n, (∫ x, (X n x) ^ 2 ∂P) ≤ C) (hY₂ : (∫ y, (Y y) ^ 2 ∂Q) ≤ C) :
    Tendsto (fun n ↦ ∫ x, |X n x| ∂P) atTop (𝓝 (∫ y, |Y y| ∂Q)) := by
  refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
  obtain ⟨R, hR⟩ := exists_gt (max 0 (3 * C / ε))
  have hR₀ : 0 < R := (le_max_left ..).trans_lt hR
  have hCR : C / R < ε / 3 := by
    have hr := (div_lt_iff₀ hε).1 ((le_max_right ..).trans_lt hR)
    apply (div_lt_iff₀ hR₀).2
    linarith
  let f := BoundedContinuousFunction.ofNormedAddCommGroup (fun x : ℝ ↦ min |x| R)
    (continuous_abs.min continuous_const) R fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (abs_nonneg _) hR₀.le)]
      exact min_le_right ..
  have hf := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    h.forall_aemeasurable h.aemeasurable_limit).1 h f
  filter_upwards [Metric.tendsto_nhds.1 hf (ε / 3) (by positivity)] with n hn
  calc
    _ ≤ dist (∫ x, |X n x| ∂P) (∫ x, f (X n x) ∂P) +
          dist (∫ x, f (X n x) ∂P) (∫ y, f (Y y) ∂Q) +
          dist (∫ y, f (Y y) ∂Q) (∫ y, |Y y| ∂Q) := dist_triangle4 _ _ _ _
    _ < ε := by
      have ha := (abs_truncation_error (hX n) hR₀).trans
        (div_le_div_of_nonneg_right (hX₂ n) hR₀.le)
      have hb := (abs_truncation_error hY hR₀).trans
        (div_le_div_of_nonneg_right hY₂ hR₀.le)
      rw [dist_comm (∫ y, f (Y y) ∂Q)]
      change dist (∫ x, min |X n x| R ∂P) (∫ y, min |Y y| R ∂Q) < ε / 3 at hn
      change dist (∫ x, |X n x| ∂P) (∫ x, min |X n x| R ∂P) +
        dist (∫ x, min |X n x| R ∂P) (∫ y, min |Y y| R ∂Q) +
        dist (∫ y, |Y y| ∂Q) (∫ y, min |Y y| R ∂Q) < ε
      linarith

private def unitIntervalLaw : Measure ℝ := volume.restrict (Icc (-1 / 2) (1 / 2))

private instance : IsProbabilityMeasure unitIntervalLaw :=
  ⟨by norm_num [unitIntervalLaw, Measure.restrict_apply, Real.volume_Icc]⟩

private def cubeLaw : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ ↦ unitIntervalLaw)

private instance : IsProbabilityMeasure cubeLaw := by
  unfold cubeLaw
  infer_instance

private def coordinate (i : ℕ) (x : ℕ → ℝ) : ℝ := x i

private lemma coordinate_preserving (i : ℕ) :
    MeasurePreserving (coordinate i) cubeLaw unitIntervalLaw :=
  measurePreserving_eval_infinitePi _ i

private lemma coordinate_uniform (i : ℕ) :
    pdf.IsUniform (coordinate i) (Icc (-1 / 2) (1 / 2)) cubeLaw := by
  refine ⟨(coordinate_preserving i).aemeasurable, ?_⟩
  rw [(coordinate_preserving i).map_eq]
  norm_num [unitIntervalLaw, ProbabilityTheory.cond, Real.volume_Icc]

private lemma coordinate_mean (i : ℕ) : ∫ x, coordinate i x ∂cubeLaw = 0 := by
  rw [(coordinate_uniform i).integral_of_Icc (by norm_num)]
  norm_num

private lemma coordinate_variance (i : ℕ) : Var[coordinate i; cubeLaw] = 1 / 12 := by
  rw [(coordinate_uniform i).variance_of_Icc (by norm_num)]
  norm_num

private lemma coordinate_memLp (i : ℕ) : MemLp (coordinate i) 2 cubeLaw := by
  have h : MemLp (id : ℝ → ℝ) 2 unitIntervalLaw :=
    (memLp_two_iff_integrable_sq continuous_id.aestronglyMeasurable).2
      ((continuous_id.pow 2).integrableOn_Icc (μ := volume))
  exact h.comp_measurePreserving (coordinate_preserving i)

private lemma coordinate_indep : iIndepFun coordinate cubeLaw :=
  iIndepFun_infinitePi (X := fun _ ↦ id) (fun _ ↦ measurable_id)

private def normalizedSum (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, coordinate i x

private lemma normalizedSum_memLp (n : ℕ) : MemLp (normalizedSum n) 2 cubeLaw :=
  (memLp_finsetSum (Finset.range n) fun i _ ↦ coordinate_memLp i).const_mul _

private lemma normalizedSum_secondMoment_le (n : ℕ) :
    (∫ x, (normalizedSum n x) ^ 2 ∂cubeLaw) ≤ 1 / 12 := by
  have hmean : ∫ x, normalizedSum n x ∂cubeLaw = 0 := by
    simp only [normalizedSum, integral_const_mul]
    rw [integral_finsetSum]
    · simp [coordinate_mean]
    · exact fun i _ ↦ (coordinate_memLp i).integrable (by simp)
  have hv : Var[normalizedSum n; cubeLaw] = (Real.sqrt (n : ℝ))⁻¹ ^ 2 * (n / 12) := by
    have hsum : normalizedSum n =
        (fun x ↦ (Real.sqrt (n : ℝ))⁻¹ * (∑ i ∈ Finset.range n, coordinate i) x) := by
      funext x
      simp only [normalizedSum, Finset.sum_apply]
    rw [hsum, variance_const_mul]
    rw [IndepFun.variance_sum (fun i _ ↦ coordinate_memLp i)
      (fun _ _ _ _ hij ↦ coordinate_indep.indepFun hij)]
    simp [coordinate_variance, div_eq_mul_inv]
  rw [variance_eq_sub (normalizedSum_memLp n), hmean, zero_pow (by decide), sub_zero] at hv
  rw [← Pi.pow_def, hv, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
    norm_num

private lemma integral_abs_normalizedSum (n : ℕ) :
    ∫ x, |normalizedSum n x| ∂cubeLaw =
      (∫ x in (Icc (fun _ : Fin n ↦ (-1 / 2 : ℝ)) (fun _ : Fin n ↦ (1 / 2 : ℝ))),
        |∑ i : Fin n, x i|) / Real.sqrt (n : ℝ) := by
  let proj (x : ℕ → ℝ) (i : Fin n) := x i
  have hmap : cubeLaw.map proj = Measure.pi (fun _ : Fin n ↦ unitIntervalLaw) := by
    simpa only [proj, cubeLaw, Measure.infinitePi_eq_pi] using
      (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ ↦ unitIntervalLaw)
        (f := (Fin.val : Fin n → ℕ)) Fin.val_injective)
  have hcube : Icc (fun _ : Fin n ↦ (-1 / 2 : ℝ)) (fun _ : Fin n ↦ (1 / 2 : ℝ)) =
      univ.pi (fun _ : Fin n ↦ Icc (-1 / 2 : ℝ) (1 / 2)) := by
    ext x
    simp [Pi.le_def]
  have hintegral : (∫ x, |∑ i : Fin n, (proj x) i| ∂cubeLaw) =
      ∫ x in (Icc (fun _ : Fin n ↦ (-1 / 2 : ℝ)) (fun _ : Fin n ↦ (1 / 2 : ℝ))),
        |∑ i : Fin n, x i| := by
    rw [hcube, volume_pi, Measure.restrict_pi_pi]
    change _ = ∫ x, |∑ i : Fin n, x i| ∂Measure.pi (fun _ : Fin n ↦ unitIntervalLaw)
    rw [← hmap]
    have hproj : Measurable proj := Measurable.of_eval fun i ↦ measurable_pi_apply i.val
    exact (integral_map (f := fun x : Fin n → ℝ ↦ |∑ i, x i|) hproj.aemeasurable
      (by fun_prop)).symm
  simp_rw [normalizedSum, ← Fin.sum_univ_eq_sum_range (fun i ↦ coordinate i _),
    abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [integral_const_mul, ← hintegral, div_eq_inv_mul]
  rfl

private lemma gaussian_mean_abs :
    (∫ x, |x| ∂gaussianReal 0 (1 / 12)) = 1 / Real.sqrt (6 * Real.pi) := by
  let c := Real.sqrt (1 / 12 : ℝ)
  have hc : 0 ≤ c := Real.sqrt_nonneg _
  have hmap : (gaussianReal 0 1).map (c * ·) = gaussianReal 0 (1 / 12) := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    ext
    norm_num [c, Real.sq_sqrt]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [abs_mul, abs_of_nonneg hc]
  rw [integral_const_mul, MathlibExt.Probability.Martingale.integral_abs_gaussianReal]
  dsimp [c]
  rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1 / 12), one_div (Real.sqrt _), ← Real.sqrt_inv]
  congr 1
  field_simp [Real.pi_ne_zero]
  ring

/-- **Mean absolute sum over the unit cube.** For $n \in \mathbb{N}$ let
$$
I_n = \int_{[-1/2,\, 1/2]^n} \left| \sum_{i=1}^n x_i \right| dx.
$$
Then $I_n / \sqrt{n} \to 1 / \sqrt{6\pi}$ as $n \to \infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_95.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem tendsto_integral_abs_sum_cube_div_sqrt
    (I : ℕ → ℝ)
    (hI : ∀ n : ℕ,
      I n = ∫ x in (Set.Icc
          (fun _ : Fin n => (-1 / 2 : ℝ))
          (fun _ : Fin n => (1 / 2 : ℝ))),
        |∑ i : Fin n, x i|) :
    Tendsto (fun n : ℕ => I n / Real.sqrt (n : ℝ)) atTop
      (𝓝 (1 / Real.sqrt (6 * Real.pi))) := by
  let Q := gaussianReal 0 (1 / 12)
  have hY : HasLaw (id : ℝ → ℝ) (gaussianReal 0 (Var[coordinate 0; cubeLaw]).toNNReal) Q := by
    rw [coordinate_variance]
    convert (HasLaw.id (μ := Q)) using 2
    ext
    norm_num [Q]
  have hclt : TendstoInDistribution normalizedSum atTop id (fun _ ↦ cubeLaw) Q := by
    have hident (i : ℕ) : IdentDistrib (coordinate i) (coordinate 0) cubeLaw cubeLaw :=
      ⟨(coordinate_preserving i).aemeasurable, (coordinate_preserving 0).aemeasurable,
        (coordinate_preserving i).map_eq.trans (coordinate_preserving 0).map_eq.symm⟩
    change TendstoInDistribution
      (fun (n : ℕ) x ↦ (Real.sqrt (n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, coordinate i x)
      atTop id (fun _ ↦ cubeLaw) Q
    simpa only [coordinate_mean, mul_zero, sub_zero] using
      tendstoInDistribution_inv_sqrt_mul_sum_sub hY (coordinate_memLp 0) coordinate_indep hident
  have hQ : MemLp (id : ℝ → ℝ) 2 Q := memLp_id_gaussianReal' _ (by simp)
  have hQ₂ : (∫ y : ℝ, y ^ 2 ∂Q) ≤ 1 / 12 := by
    have h := variance_eq_sub hQ
    simpa [Q, integral_id_gaussianReal, variance_id_gaussianReal, Pi.pow_apply] using h.ge
  have h := tendsto_integral_abs_of_secondMoment_le hclt normalizedSum_memLp hQ
    normalizedSum_secondMoment_le hQ₂
  simp_rw [hI]
  simpa only [id, Q, gaussian_mean_abs, integral_abs_normalizedSum] using h

end

end MathlibExt.MeasureTheory.CubeAbsSumIntegralAsymptoticWanted
