/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_47.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029):
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors: L. Pu et al. (MA-ProofBench, arXiv:2606.13782).

This attribution applies to the theorem statement and its documentation.

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
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Bernstein inequality for Schwartz functions with Fourier support of finite measure

Fourier inversion and Plancherel give the Bernstein bound from `Lᵖ` to `Lᑫ` with constant one
when `1 ≤ p ≤ q` and `p ≤ 2`.
-/

public section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace MathlibExt.Analysis.Fourier.BernsteinFourierSupportLpLqWanted

-- Compare the Fourier norms on E, then use Plancherel to return to the spatial side.
private lemma fourier_l1_le {n : ℕ} (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : MeasurableSet E) (hvol : volume E < ⊤)
    (hs : tsupport (fun ξ ↦ (𝓕 f) ξ) ⊆ E) :
    ‖(𝓕 f).toLp 1‖ ≤ (volume E).toReal ^ (1 / 2 : ℝ) * ‖f.toLp 2‖ := by
  let g : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ ↦ (𝓕 f) ξ
  have hind : E.indicator g = g := Set.indicator_eq_self.2 ((subset_tsupport g).trans hs)
  have hres (r : ℝ≥0∞) : eLpNorm g r (volume.restrict E) = eLpNorm g r volume := by
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hE.nullMeasurableSet, hind]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict E)
    (p := 1) (q := 2) (by norm_num) (𝓕 f).continuous.aestronglyMeasurable
  change eLpNorm g 1 _ ≤ eLpNorm g 2 _ * _ at h
  rw [hres, hres, Measure.restrict_apply_univ] at h
  norm_num at h
  have hreal := ENNReal.toReal_mono (ne_of_lt (ENNReal.mul_lt_top ((𝓕 f).eLpNorm_lt_top 2)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hvol.ne))) h
  rw [← SchwartzMap.norm_fourier_toL2_eq f, SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  simpa [g, ENNReal.toReal_mul, ENNReal.toReal_rpow, mul_comm] using hreal

-- Integrating |f|^q ≤ M^(q-p) |f|^p compares finite moments using a pointwise bound.
private lemma moment_le {n : ℕ} (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) {p q : ℝ≥0∞} (hp : 0 < p) (hpq : p ≤ q)
    (hq : q ≠ ⊤) :
    ‖f.toLp q‖ ^ q.toReal ≤ M ^ (q.toReal - p.toReal) * ‖f.toLp p‖ ^ p.toReal := by
  have hpt := (hpq.trans_lt (lt_top_iff_ne_top.mpr hq)).ne
  have hq₀ := hp.trans_le hpq
  have hp' := ENNReal.toReal_pos hp.ne' hpt
  have hq' := ENNReal.toReal_pos hq₀.ne' hq
  have hdiff := sub_nonneg.mpr (ENNReal.toReal_mono hq hpq)
  rw [SchwartzMap.norm_toLp' hq₀.ne' hq, SchwartzMap.norm_toLp' hp.ne' hpt,
    Real.rpow_inv_rpow (by positivity) hq'.ne', Real.rpow_inv_rpow (by positivity) hp'.ne',
    ← integral_const_mul]
  apply integral_mono ((f.memLp q volume).integrable_norm_rpow hq₀.ne' hq)
    (((f.memLp p volume).integrable_norm_rpow hp.ne' hpt).const_mul (M ^ (q.toReal - p.toReal)))
  intro x
  calc
    ‖f x‖ ^ q.toReal = ‖f x‖ ^ (q.toReal - p.toReal) * ‖f x‖ ^ p.toReal := by
      rw [← Real.rpow_add_of_nonneg (norm_nonneg _) hdiff hp'.le, sub_add_cancel]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg _) (hM x) hdiff)
      (by positivity)

-- Cancel the common power of M in the second-moment estimate.
private lemma bound_of_second_moment {M V A B p : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hp : 0 < p) (hsq : M ^ (2 : ℝ) ≤ V * B) (hm : B ≤ M ^ (2 - p) * A ^ p) :
    M ≤ V ^ (1 / p) * A := by
  rcases hM.eq_or_lt with hzero | hpos
  · rw [← hzero]
    exact mul_nonneg (Real.rpow_nonneg hV _) hA
  apply (Real.rpow_le_rpow_iff hM (mul_nonneg (Real.rpow_nonneg hV _) hA) hp).mp
  rw [Real.mul_rpow (Real.rpow_nonneg hV _) hA, one_div, Real.rpow_inv_rpow hV hp.ne']
  apply le_of_mul_le_mul_left (a := M ^ (2 - p)) _ (Real.rpow_pos_of_pos hpos _)
  calc
    M ^ (2 - p) * M ^ p = M ^ (2 : ℝ) := by rw [← Real.rpow_add hpos, sub_add_cancel]
    _ ≤ V * B := hsq
    _ ≤ V * (M ^ (2 - p) * A ^ p) := mul_le_mul_of_nonneg_left hm hV
    _ = _ := by ring

-- Taking the q-th root of the moment bound yields the difference of reciprocal exponents.
private lemma bound_of_moment {M V A B p q : ℝ} (hM : 0 ≤ M) (hV : 0 ≤ V) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hp : 0 < p) (hpq : p ≤ q) (hbound : M ≤ V ^ (1 / p) * A)
    (hm : B ^ q ≤ M ^ (q - p) * A ^ p) : B ≤ V ^ (1 / p - q⁻¹) * A := by
  have hq := hp.trans_le hpq
  have hdiff := sub_nonneg.mpr hpq
  apply (Real.rpow_le_rpow_iff hB (mul_nonneg (Real.rpow_nonneg hV _) hA) hq).mp
  calc
    B ^ q ≤ M ^ (q - p) * A ^ p := hm
    _ ≤ (V ^ (1 / p) * A) ^ (q - p) * A ^ p :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hM hbound hdiff) (Real.rpow_nonneg hA _)
    _ = (V ^ (1 / p - q⁻¹) * A) ^ q := by
      rw [Real.mul_rpow (Real.rpow_nonneg hV _) hA, mul_assoc,
        ← Real.rpow_add_of_nonneg hA hdiff hp.le, sub_add_cancel,
        Real.mul_rpow (Real.rpow_nonneg hV _) hA, ← Real.rpow_mul hV, ← Real.rpow_mul hV]
      rw [show 1 / p * (q - p) = (1 / p - q⁻¹) * q by field_simp]

/-- **Bernstein inequality for Schwartz functions with Fourier support of finite measure.**
Fix $n \in \mathbb{N}$. For a Schwartz function $f : \mathbb{R}^n \to \mathbb{C}$ write
$\hat f(\xi) = \int_{\mathbb{R}^n} f(x) e^{-2\pi i \langle x, \xi \rangle}\,dx$ for its Fourier
transform, and write $|E|$ for the Lebesgue measure of a set $E \subseteq \mathbb{R}^n$. There
is a constant $C > 0$ such that for every Borel set $E \subseteq \mathbb{R}^n$ with
$|E| < \infty$, all $p, q \in [1, \infty]$ with $p \le q$ and $p \le 2$, and every Schwartz
function $f : \mathbb{R}^n \to \mathbb{C}$ whose Fourier transform has closed support
$\overline{\{\xi : \hat f(\xi) \ne 0\}}$ contained in $E$,
$$\|f\|_{L^q(\mathbb{R}^n)} \le C\, |E|^{1/p - 1/q}\, \|f\|_{L^p(\mathbb{R}^n)},$$
where $1/q = 0$ for $q = \infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis;
Distributions, generalized functions, distribution spaces),
`benchmark/level2/ma_proofbench_l2_47.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exists_const_norm_toLp_le_volume_rpow_mul_norm_toLp_of_tsupport_fourier_subset
    {n : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ (E : Set (EuclideanSpace ℝ (Fin n))),
        MeasurableSet E →
        (MeasureTheory.volume E) < ⊤ →
        ∀ p q : ENNReal,
          1 ≤ p → p ≤ q → q ≤ ⊤ → p ≤ 2 →
            ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
              tsupport (fun ξ : EuclideanSpace ℝ (Fin n) => (𝓕 f) ξ) ⊆ E →
                ‖f.toLp q
                    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))‖ ≤
                  C *
                    Real.rpow (MeasureTheory.volume E).toReal
                      (1 / p.toReal -  (1 / q).toReal) *
                    ‖f.toLp p
                      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))‖
    := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro E hE hvol p q hp hpq _ hp₂ f hs
  have hnorm (r : ℝ≥0∞) : 0 ≤ ‖f.toLp r volume‖ := by
    rw [SchwartzMap.norm_toLp]
    exact ENNReal.toReal_nonneg
  let M : ℝ := ‖(𝓕 f).toLp 1‖
  have hM₀ : 0 ≤ M := norm_nonneg ((𝓕 f).toLp 1 volume)
  have hM : ∀ x, ‖f x‖ ≤ M := by
    intro x
    calc
      ‖f x‖ = ‖(𝓕⁻ (𝓕 f)) x‖ := by rw [FourierTransform.fourierInv_fourier_eq]
      _ ≤ M := SchwartzMap.norm_fourier_apply_le_toLp_one (𝓕 f) (-x)
  have hp₀ := zero_lt_one.trans_le hp
  have hp' := ENNReal.toReal_pos hp₀.ne' (hp₂.trans_lt (by norm_num : (2 : ℝ≥0∞) < ⊤)).ne
  have hV := ENNReal.toReal_nonneg (a := volume E)
  -- Squaring the frequency-side bound and using the second moment gives M^p ≤ |E| ‖f‖ₚ^p.
  have hbound : M ≤ (volume E).toReal ^ (1 / p.toReal) * ‖f.toLp p‖ := by
    refine bound_of_second_moment hM₀ hV (hnorm p) hp' (B := ‖f.toLp 2 volume‖ ^ (2 : ℝ)) ?_ ?_
    · have hsq := Real.rpow_le_rpow (norm_nonneg _) (fourier_l1_le f hE hvol hs)
          (by norm_num : (0 : ℝ) ≤ 2)
      rw [Real.mul_rpow (by positivity) (norm_nonneg _), ← Real.rpow_mul hV] at hsq
      simpa only [one_div, inv_mul_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0), Real.rpow_one] using hsq
    · simpa only [ENNReal.toReal_ofNat] using moment_le f hM hp₀ hp₂ (by norm_num)
  rw [one_mul, one_div q, ENNReal.toReal_inv]
  rcases eq_or_ne q ⊤ with rfl | hq
  · simp only [ENNReal.toReal_top, inv_zero, sub_zero]
    apply le_trans _ hbound
    rw [SchwartzMap.norm_toLp, eLpNorm_exponent_top f.continuous.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) (eLpNormEssSup_le_of_ae_bound
      (.of_forall hM))
  exact bound_of_moment hM₀ hV (hnorm p) (hnorm q) hp' (ENNReal.toReal_mono hq hpq) hbound
    (moment_le f hM hp₀ hpq hq)

end MathlibExt.Analysis.Fourier.BernsteinFourierSupportLpLqWanted
