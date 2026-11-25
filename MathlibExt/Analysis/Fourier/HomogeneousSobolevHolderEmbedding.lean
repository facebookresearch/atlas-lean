/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_21.lean` (MA-ProofBench, openbmb/ma-proofbench@31bab4c):
the homogeneous seminorm definition and the embedding statement.
Authors: L. Pu et al.
Licensed under the MIT License.

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
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Homogeneous Sobolev embedding on the real line

For Schwartz functions, the homogeneous Sobolev seminorm of order `s ∈ (1/2, 1]` bounds
the Hölder seminorm of order `s - 1/2`.
-/

@[expose] public section

open MeasureTheory
open scoped FourierTransform

namespace MathlibExt.Analysis.Fourier.HomogeneousSobolevHolderEmbeddingWanted

/-- **Homogeneous Sobolev seminorm for the Hölder embedding.** For a real number $s$ and a
Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with Fourier transform
$\hat f(\xi) = \int_{\mathbb{R}} e^{-2\pi i x \xi} f(x) \, dx$, the homogeneous Sobolev seminorm
of $f$ is
$$
\|f\|_{\dot H^s} = \left( \int_{\mathbb{R}} |\xi|^{2s} \, |\hat f(\xi)|^2 \, d\xi \right)^{1/2},
$$
where the integral is taken to be $0$ when the integrand is not integrable. -/
noncomputable def dotHSeminorm (s : ℝ) (f : SchwartzMap ℝ ℂ) : ℝ :=
  Real.sqrt (∫ ξ : ℝ, Real.rpow ‖ξ‖ (2 * s) * ‖(𝓕 f) ξ‖ ^ 2)

/-- After removing the phase at the second point, a Fourier character difference is
bounded linearly at the origin and uniformly at infinity. -/
private lemma character_bound {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) (t : ℝ) :
    ‖(𝐞 t : ℂ) - 1‖ ≤ 4 * Real.pi * (1 + ‖t‖) ^ (-s) * ‖t‖ ^ s := by
  have hbase : 0 < 1 + ‖t‖ := by positivity
  rw [Real.rpow_neg hbase.le, mul_right_comm, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  by_cases ht : ‖t‖ ≤ 1
  · have hchar : ‖(𝐞 t : ℂ) - 1‖ ≤ 2 * Real.pi * ‖t‖ := by
      simpa only [Real.fourierChar_apply, mul_comm Complex.I, norm_mul,
        Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        using Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi * t)
    have hpow : (1 + ‖t‖) ^ s ≤ 2 :=
      (Real.rpow_le_self_of_one_le (by linarith [norm_nonneg t]) hs').trans (by linarith)
    calc
      _ ≤ (2 * Real.pi * ‖t‖) * 2 := mul_le_mul hchar hpow (by positivity) (by positivity)
      _ ≤ (2 * Real.pi * ‖t‖ ^ s) * 2 := by
        gcongr
        exact Real.self_le_rpow_of_le_one (norm_nonneg _) ht hs'
      _ = _ := by ring
  · have hchar : ‖(𝐞 t : ℂ) - 1‖ ≤ 2 := by
      simpa [← one_add_one_eq_two] using norm_sub_le (𝐞 t : ℂ) 1
    have hpow : (1 + ‖t‖) ^ s ≤ 2 * ‖t‖ ^ s := calc
      _ ≤ (2 * ‖t‖) ^ s := Real.rpow_le_rpow hbase.le (by linarith) hs
      _ = (2 : ℝ) ^ s * ‖t‖ ^ s := Real.mul_rpow (by norm_num) (norm_nonneg _)
      _ ≤ _ := by gcongr; exact Real.rpow_le_self_of_one_le (by norm_num) hs'
    calc
      _ ≤ 2 * (2 * ‖t‖ ^ s) := mul_le_mul hchar hpow (by positivity) (by norm_num)
      _ ≤ 4 * Real.pi * ‖t‖ ^ s := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (by linarith [Real.two_le_pi]) (by positivity)

private lemma memLp_weighted {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) (g : SchwartzMap ℝ ℂ) :
    MemLp (fun ξ : ℝ ↦ ‖ξ‖ ^ s * ‖g ξ‖) 2 := by
  have hlin : MemLp (fun ξ : ℝ ↦ ‖ξ‖ * ‖g ξ‖) 2 := by
    simpa only [SchwartzMap.smulLeftCLM_apply_apply (g := (id : ℝ → ℝ)) (by fun_prop), id_eq,
      norm_smul] using ((SchwartzMap.smulLeftCLM ℂ (id : ℝ → ℝ) g).memLp 2).norm
  refine ((g.memLp 2 volume).norm.add hlin).mono' ?_ ?_
  · fun_prop
  filter_upwards with ξ
  have h : ‖ξ‖ ^ s ≤ 1 + ‖ξ‖ := by
    by_cases hξ : ‖ξ‖ ≤ 1
    · linarith [Real.rpow_le_one (norm_nonneg ξ) hξ hs, norm_nonneg ξ]
    · linarith [Real.rpow_le_self_of_one_le (le_of_not_ge hξ) hs']
  simp only [Real.norm_of_nonneg (by positivity : 0 ≤ ‖ξ‖ ^ s * ‖g ξ‖), Pi.add_apply]
  simpa only [add_mul, one_mul] using
    mul_le_mul_of_nonneg_right h (norm_nonneg (g ξ))

private lemma norm_sub_le_fourier_integral (f : SchwartzMap ℝ ℂ) (x y : ℝ) :
    ‖f x - f y‖ ≤ ∫ ξ : ℝ, ‖(𝐞 ((x - y) * ξ) : ℂ) - 1‖ * ‖(𝓕 f) ξ‖ := by
  let g := 𝓕 f
  let F (z ξ : ℝ) := (𝐞 (z * ξ) : ℂ) * g ξ
  have hF (z : ℝ) : Integrable (F z) := by
    refine (g.integrable (μ := volume)).norm.mono' ?_ (.of_forall fun ξ ↦ ?_)
    · dsimp [F]
      fun_prop
    · simp [F]
  have hinv (z : ℝ) : f z = ∫ ξ, F z ξ := calc
    f z = (𝓕⁻ g) z := by simp [g]
    _ = _ := by simp [SchwartzMap.fourierInv_coe, Real.fourierInv_eq,
      Circle.smul_def, F, mul_comm z]
  rw [hinv x, hinv y, ← integral_sub (hF x) (hF y)]
  refine (norm_integral_le_integral_norm _).trans_eq (integral_congr_ae (.of_forall fun ξ ↦ ?_))
  have hxy : x * ξ = (x - y) * ξ + y * ξ := by ring
  simp only [F, hxy, AddChar.map_add_eq_mul, Circle.coe_mul, ← sub_mul, norm_mul,
    ← sub_one_mul (↑(𝐞 ((x - y) * ξ)) : ℂ), Circle.norm_coe, mul_one, g]

/-- The change of variable in the squared kernel supplies the half power in the exponent. -/
private lemma sqrt_integral_dilate (K : ℝ → ℝ) (h : ℝ) :
    Real.sqrt (∫ ξ : ℝ, K (h * ξ) ^ 2) =
      ‖h‖ ^ (-(1 / 2 : ℝ)) * Real.sqrt (∫ ξ : ℝ, K ξ ^ 2) := by
  rw [Measure.integral_comp_mul_left (fun t ↦ K t ^ 2), smul_eq_mul,
    Real.sqrt_mul (abs_nonneg _), abs_inv, Real.sqrt_inv, Real.rpow_neg (norm_nonneg h),
    ← Real.sqrt_eq_rpow, Real.norm_eq_abs]

/-- **The homogeneous Sobolev seminorm controls the Hölder seminorm.** Let $s \in (\tfrac12, 1]$,
and for a Schwartz function $f : \mathbb{R} \to \mathbb{C}$ with Fourier transform $\hat f$ let
$\|f\|_{\dot H^s} = \left( \int_{\mathbb{R}} |\xi|^{2s} |\hat f(\xi)|^2 \, d\xi \right)^{1/2}$
be its homogeneous Sobolev seminorm. There is a constant $C_3 > 0$ such that for every Schwartz
function $f : \mathbb{R} \to \mathbb{C}$,
$$
\sup_{x \ne y} \frac{|f(x) - f(y)|}{|x - y|^{s - \frac12}} \le C_3 \, \|f\|_{\dot H^s}.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_21.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_holderSeminorm_le_mul_dotHSeminorm
    (s : ℝ) (hs : s ∈ Set.Ioc (1 / 2 : ℝ) 1) :
    ∃ C3 > 0, ∀ f : SchwartzMap ℝ ℂ,
      sSup
          (Set.range
            (fun p : {xy : ℝ × ℝ // xy.1 ≠ xy.2} =>
              ‖f p.1.1 - f p.1.2‖ / Real.rpow ‖p.1.1 - p.1.2‖ (s - 1 / 2)))
        ≤ C3 * dotHSeminorm s f := by
  have hs₀ : 0 ≤ s := by linarith [hs.1]
  let K (t : ℝ) := (1 + ‖t‖) ^ (-s)
  have hK (t : ℝ) : 0 ≤ K t := by dsimp [K]; positivity
  have hK₂ : Integrable (fun t : ℝ ↦ K t ^ 2) := by
    have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 * s := by
      simp only [Module.finrank_self, Nat.cast_one]
      linarith [hs.1]
    convert (integrable_one_add_norm (μ := volume) hdim) using 1
    ext t
    simp only [K, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + ‖t‖)]
    congr 1
    push_cast
    ring
  let A := Real.sqrt (∫ t : ℝ, K t ^ 2)
  refine ⟨4 * Real.pi * (A + 1), by dsimp [A]; positivity, fun f ↦ ?_⟩
  apply csSup_le
  · exact ⟨_, ⟨⟨(0, 1), zero_ne_one⟩, rfl⟩⟩
  rintro _ ⟨⟨⟨x, y⟩, hxy⟩, rfl⟩
  dsimp only
  let h := x - y
  have hh : h ≠ 0 := sub_ne_zero.mpr hxy
  have hh₀ : 0 < ‖h‖ := norm_pos_iff.mpr hh
  let G (ξ : ℝ) := ‖ξ‖ ^ s * ‖(𝓕 f) ξ‖
  have hG (ξ : ℝ) : 0 ≤ G ξ := by dsimp [G]; positivity
  have hG₂ : MemLp G 2 := memLp_weighted hs₀ hs.2 (𝓕 f)
  have hKh : MemLp (fun ξ ↦ K (h * ξ)) 2 := by
    refine (memLp_two_iff_integrable_sq ?_).2 (hK₂.comp_mul_left' hh)
    apply Continuous.aestronglyMeasurable
    exact (continuous_const.add (continuous_const.mul continuous_id).norm).rpow_const
      (fun ξ ↦ Or.inl (show 1 + ‖h * ξ‖ ≠ 0 by positivity))
  have hcs : (∫ ξ : ℝ, K (h * ξ) * G ξ) ≤
      (‖h‖ ^ (-(1 / 2 : ℝ)) * A) * dotHSeminorm s f := by
    have hsq (ξ : ℝ) : G ξ ^ 2 = ‖ξ‖ ^ (2 * s) * ‖(𝓕 f) ξ‖ ^ 2 := by
      dsimp only [G]
      rw [mul_pow, mul_comm 2 s, ← Real.rpow_mul_natCast (norm_nonneg ξ)]
      norm_num
    rw [← sqrt_integral_dilate K h]
    simpa only [← Real.sqrt_eq_rpow, Real.rpow_two, hsq, dotHSeminorm, Real.rpow_eq_pow] using
      integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
        (.of_forall fun ξ ↦ hK (h * ξ)) (.of_forall hG)
        (by simpa using hKh) (by simpa using hG₂)
  have hbound : ‖f x - f y‖ ≤ 4 * Real.pi * ‖h‖ ^ s * (∫ ξ : ℝ, K (h * ξ) * G ξ) := by
    refine (norm_sub_le_fourier_integral f x y).trans ?_
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg
    · exact .of_forall fun ξ ↦ by positivity
    · exact (hKh.integrable_mul hG₂).const_mul _
    · filter_upwards with ξ
      calc
        _ ≤ (4 * Real.pi * K (h * ξ) * ‖h * ξ‖ ^ s) * ‖(𝓕 f) ξ‖ :=
          mul_le_mul_of_nonneg_right (character_bound hs₀ hs.2 (h * ξ)) (norm_nonneg _)
        _ = _ := by rw [norm_mul, Real.mul_rpow (norm_nonneg h) (norm_nonneg ξ)]; dsimp [G]; ring
  change ‖f x - f y‖ / ‖h‖ ^ (s - 1 / 2) ≤ _
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hh₀ _)).2
  calc
    _ ≤ _ := hbound
    _ ≤ 4 * Real.pi * ‖h‖ ^ s * ((‖h‖ ^ (-(1 / 2 : ℝ)) * A) * dotHSeminorm s f) := by
      gcongr
    _ = 4 * Real.pi * A * dotHSeminorm s f * ‖h‖ ^ (s - 1 / 2) := by
      rw [sub_eq_add_neg, Real.rpow_add hh₀]
      ring
    _ ≤ _ := by
      have : 0 ≤ dotHSeminorm s f := Real.sqrt_nonneg _
      gcongr
      linarith

end MathlibExt.Analysis.Fourier.HomogeneousSobolevHolderEmbeddingWanted
