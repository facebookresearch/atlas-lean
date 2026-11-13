/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fejér's theorem

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
the definitions `fourierPartialSum` and `fourierCesaroMean` and the statement of
`tendstoUniformly_fourierCesaroMean` are taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.FourierConvergence` —
fourier_dirichlet_fejer (manifest `manifests/problems/fourier_dirichlet_fejer.toml`, rev 1,
submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: moved here from the `theorem_wanted` `fejer` in
`WantedExt/Analysis/FourierConvergenceWanted.lean`, renamed it
`tendstoUniformly_fourierCesaroMean`, placed the declarations in the
`MathlibExt.Analysis.Fourier` namespace, and proved the statement. Mathematical
statements are unchanged. Source: L. Fejér (1900). Listed as §46 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fejér's theorem

For a continuous `2π`-periodic `f : ℝ → ℂ`, the Cesàro means
`σ_N f = (S_0 f + ⋯ + S_N f) / (N + 1)` of the symmetric Fourier partial sums
`S_N f x = ∑_{|n| ≤ N} f̂ₙ e^{inx}` converge to `f` uniformly on `ℝ`
(`tendstoUniformly_fourierCesaroMean`). The coefficients `f̂ₙ` are Mathlib's
`fourierCoeffOn Real.two_pi_pos f n`.

Mathlib has the Fourier coefficients and the `L²` theory of Fourier series on `AddCircle`, but
no Dirichlet or Fejér kernel, Cesàro means, or Fejér theorem.

## Proof

`S_k f` is the convolution of `f` with the Dirichlet kernel `D_k y = 1 + 2 ∑_{j=1}^{k} cos (j y)`
(`partialSum_eq_integral_dirichletKernel`), so `σ_N f` is the convolution with the Fejér kernel
`F_{N+1} = (D_0 + ⋯ + D_N) / (N + 1) = sin² ((N + 1) y / 2) / ((N + 1) sin² (y / 2))`
(`cesaroMean_eq_integral_fejerKernel`). `F_N` is a nonnegative approximate identity: it has
mean one and its mass outside `[-δ, δ]` tends to zero, so convolution with it converges
uniformly to a continuous periodic real function (`fejer_uniform_convergence`). The kernel is
real, so the complex statement follows from the real and imaginary parts.

## Provenance

The approximate-identity argument and the Fejér kernel estimates are a code-derived port of
`ApproximateIdentity.approximate_identity_lemma`, `FejerL1Density.fejer_uniform_convergence`,
`FejerL1Density.fejerKernel_eq_dirichlet_avg` and their helpers from
`v1/Atlas/FourierAnalysis/code/FourierSeries.lean` at commit
`6191bf1ba03d204784385ef5be2472be88035b93`, lines 69–319, 341–590, 976–1143 and 1253–1312.
Uniform continuity of periodic functions is taken from compactness of `AddCircle` instead of
the archived ε-δ proof, and the archived subinterval bound from
`intervalIntegral.integral_mono_interval`. The Dirichlet-kernel form of `fourierCoeffOn`
partial sums and the complex statement are new. The archived formalization and its original
license/provenance remain in `v1/` (the original license text is `v1/LICENSE`). The archived
code supplies proof steps only; the public statement is the lean-eval one above.
-/

set_option autoImplicit false

open MeasureTheory Filter Topology Set intervalIntegral Real

namespace MathlibExt.Analysis.Fourier

noncomputable def periodicConvolution (f K : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ y in (-π)..π, f (x - y) * K y

lemma periodic_continuous_uniformContinuous {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : Continuous f) (hper : Function.Periodic f p) : UniformContinuous f := by
  have : Fact (0 < p) := ⟨hp⟩
  have hmk : UniformContinuous ((↑) : ℝ → AddCircle p) :=
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples p)).uniformContinuous_of_continuousAt_zero
      continuous_quotient_mk'.continuousAt
  exact (CompactSpace.uniformContinuous_of_continuous
    (continuous_coinduced_dom.mpr hf : Continuous hper.lift)).comp hmk

lemma convolution_sub_eq (f K : ℝ → ℝ) (x : ℝ)
    (hK : IntervalIntegrable K volume (-π) π)
    (hfK : IntervalIntegrable (fun y => f (x - y) * K y) volume (-π) π)
    (hnorm : (1 / (2 * π)) * ∫ y in (-π)..π, K y = 1) :
    periodicConvolution f K x - f x =
      (1 / (2 * π)) * ∫ y in (-π)..π, (f (x - y) - f x) * K y := by
  unfold periodicConvolution
  have hint_K_val : ∫ y in (-π)..π, K y = 2 * π := by
    have : (1 : ℝ) / (2 * π) ≠ 0 := by positivity
    field_simp at hnorm; linarith
  have key : ∫ y in (-π)..π, (f (x - y) - f x) * K y =
      (∫ y in (-π)..π, f (x - y) * K y) - f x * (∫ y in (-π)..π, K y) := by
    rw [show (fun y => (f (x - y) - f x) * K y) = (fun y => f (x - y) * K y - f x * K y) from
      by ext y; ring, integral_sub hfK (hK.const_mul (f x)),
      intervalIntegral.integral_const_mul]
  rw [key, hint_K_val]; field_simp

theorem approximate_identity_lemma
    (f : ℝ → ℝ) (K : ℕ → ℝ → ℝ)
    (hf_cont : Continuous f)
    (hf_periodic : Function.Periodic f (2 * π))
    (hK_intble : ∀ N, IntervalIntegrable (K N) volume (-π) π)
    (hfK_intble : ∀ N x, IntervalIntegrable (fun y => f (x - y) * K N y) volume (-π) π)
    (habs_K_intble : ∀ N, IntervalIntegrable (fun y => |K N y|) volume (-π) π)
    (hdiff_K_intble : ∀ N x,
      IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-π) π)
    (h_normalize : ∀ N, (1 / (2 * π)) * ∫ x in (-π)..π, K N x = 1)
    (h_bound : ∃ M : ℝ, ∀ N, ∫ x in (-π)..π, |K N x| ≤ M)
    (h_concentrate : ∀ δ, 0 < δ → δ ≤ π →
      Filter.Tendsto (fun N => (∫ x in (-π)..(-δ), |K N x|) + ∫ x in δ..π, |K N x|)
        Filter.atTop (nhds 0)) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ℝ,
      |f x - periodicConvolution f (K N) x| ≤ ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := h_bound
  have hM_nonneg : 0 ≤ M := le_trans
    (intervalIntegral.integral_nonneg (by linarith [pi_pos]) (fun u _ => abs_nonneg _)) (hM 0)
  have hf_uc := periodic_continuous_uniformContinuous (by positivity : (0 : ℝ) < 2 * π)
    hf_cont hf_periodic
  have hf_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |f z| ≤ C := by
    have hne : (Icc (0 : ℝ) (2 * π)).Nonempty := nonempty_Icc.mpr (by positivity)
    obtain ⟨x₀, _, hx₀_max⟩ :=
      isCompact_Icc.exists_isMaxOn hne hf_cont.abs.continuousOn
    refine ⟨|f x₀|, abs_nonneg _, fun z => ?_⟩
    set n := ⌊z / (2 * π)⌋
    rw [show f z = f (z - n • (2 * π)) from (hf_periodic.sub_zsmul_eq n).symm]
    apply hx₀_max
    simp only [zsmul_eq_mul]
    have h2pi_pos : (0 : ℝ) < 2 * π := by positivity
    have hlb : (⌊z / (2 * π)⌋ : ℝ) * (2 * π) ≤ z := by
      rw [← le_div_iff₀ h2pi_pos]; exact Int.floor_le _
    have hub : z < ((⌊z / (2 * π)⌋ : ℝ) + 1) * (2 * π) := by
      rw [← div_lt_iff₀ h2pi_pos]; exact Int.lt_floor_add_one _
    exact ⟨by linarith, by linarith⟩
  obtain ⟨C, hC_nonneg, hC⟩ := hf_bdd
  rw [Metric.uniformContinuous_iff] at hf_uc
  obtain ⟨δ, hδ_pos, hδ_uc⟩ := hf_uc (ε * π / (M + 1)) (by positivity)
  set δ' := min (δ / 2) π with hδ'_def
  have hδ'_pos : 0 < δ' := lt_min (by linarith) pi_pos
  have hδ'_le_π : δ' ≤ π := min_le_right _ _
  have hneg_π_le_neg_δ' : -π ≤ -δ' := by linarith
  have huc_bound : ∀ x y : ℝ, |y| ≤ δ' → |f (x - y) - f x| ≤ ε * π / (M + 1) := by
    intro x y hy
    exact le_of_lt (hδ_uc (by
      rw [dist_eq_norm, show (x - y) - x = -y from by ring, norm_neg, Real.norm_eq_abs]
      exact lt_of_le_of_lt hy (lt_of_le_of_lt (min_le_left _ _) (by linarith))))
  have h_conc_δ := h_concentrate δ' hδ'_pos hδ'_le_π
  rw [Metric.tendsto_atTop] at h_conc_δ
  obtain ⟨N₀, hN₀⟩ := h_conc_δ (ε * π / (2 * C + 1)) (by positivity)
  have htail : ∀ N ≥ N₀,
      (∫ y in (-π)..(-δ'), |K N y|) + ∫ y in δ'..π, |K N y| < ε * π / (2 * C + 1) := by
    intro N hN
    have h_dist := hN₀ N hN
    rw [Real.dist_eq, sub_zero] at h_dist
    rwa [abs_of_nonneg] at h_dist
    apply add_nonneg
    · exact intervalIntegral.integral_nonneg hneg_π_le_neg_δ' (fun u _ => abs_nonneg _)
    · exact intervalIntegral.integral_nonneg hδ'_le_π (fun u _ => abs_nonneg _)
  use N₀
  intro N hN x
  have h_eq := convolution_sub_eq f (K N) x (hK_intble N) (hfK_intble N x) (h_normalize N)
  rw [abs_sub_comm]
  rw [h_eq]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  have hpi_le : (-π : ℝ) ≤ π := by linarith [pi_pos]
  have hnorm_le := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hpi_le
    (f := fun y => (f (x - y) - f x) * K N y)
  simp only [Real.norm_eq_abs] at hnorm_le
  have habs_sub : IntervalIntegrable (fun y => |K N y|) volume (-π) π := habs_K_intble N
  have hdiff_sub : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-π) π :=
    hdiff_K_intble N x
  have hsub : ∀ {a b : ℝ}, -π ≤ a → a ≤ b → b ≤ π → uIcc a b ⊆ uIcc (-π) π :=
    fun ha hab hb => by rw [uIcc_of_le hab, uIcc_of_le hpi_le]; exact Icc_subset_Icc ha hb
  have habs_sub_1 : IntervalIntegrable (fun y => |K N y|) volume (-π) (-δ') :=
    habs_sub.mono_set (hsub le_rfl hneg_π_le_neg_δ' (by linarith))
  have habs_sub_2 : IntervalIntegrable (fun y => |K N y|) volume (-δ') δ' :=
    habs_sub.mono_set (hsub (by linarith) (by linarith) hδ'_le_π)
  have habs_sub_3 : IntervalIntegrable (fun y => |K N y|) volume δ' π :=
    habs_sub.mono_set (hsub (by linarith) hδ'_le_π le_rfl)
  have hdiff_sub_1 : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-π) (-δ') :=
    hdiff_sub.mono_set (hsub le_rfl hneg_π_le_neg_δ' (by linarith))
  have hdiff_sub_2 : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-δ') δ' :=
    hdiff_sub.mono_set (hsub (by linarith) (by linarith) hδ'_le_π)
  have hdiff_sub_3 : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume δ' π :=
    hdiff_sub.mono_set (hsub (by linarith) hδ'_le_π le_rfl)
  have h_split : ∫ y in (-π)..π, |(f (x - y) - f x) * K N y| =
      (∫ y in (-π)..(-δ'), |(f (x - y) - f x) * K N y|)
      + (∫ y in (-δ')..δ', |(f (x - y) - f x) * K N y|)
      + ∫ y in δ'..π, |(f (x - y) - f x) * K N y| := by
    have h_abs_eq : (fun y => |(f (x - y) - f x) * K N y|) =
        (fun y => |f (x - y) - f x| * |K N y|) :=
      by ext y; exact abs_mul _ _
    have h_abs_intble :
        IntervalIntegrable (fun y => |(f (x - y) - f x) * K N y|) volume (-π) π := by
      rw [h_abs_eq]; exact hdiff_K_intble N x
    have h_abs_intble_1 := h_abs_intble.mono_set (hsub le_rfl hneg_π_le_neg_δ' (by linarith))
    have h_abs_intble_2 :=
      h_abs_intble.mono_set (hsub (a := -δ') (by linarith) (by linarith) hδ'_le_π)
    have h_abs_intble_3 := h_abs_intble.mono_set (hsub (by linarith) hδ'_le_π le_rfl)
    have h12 := integral_add_adjacent_intervals h_abs_intble_1 h_abs_intble_2
    have h123 :=
      integral_add_adjacent_intervals (h_abs_intble_1.trans h_abs_intble_2) h_abs_intble_3
    rw [← h123, ← h12]
  have h_near : ∫ y in (-δ')..δ', |f (x - y) - f x| * |K N y| ≤
      ε * π / (M + 1) * ∫ y in (-δ')..δ', |K N y| := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on (by linarith) hdiff_sub_2 (habs_sub_2.const_mul _)
    intro y hy
    exact mul_le_mul_of_nonneg_right
      (huc_bound x y (by rw [abs_le]; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩))
      (abs_nonneg _)
  have h_near_K_le : ∫ y in (-δ')..δ', |K N y| ≤ M :=
    le_trans (integral_mono_interval hneg_π_le_neg_δ' (by linarith) hδ'_le_π
      (Eventually.of_forall fun _ => abs_nonneg _) (habs_K_intble N)) (hM N)
  have h_far1 : ∫ y in (-π)..(-δ'), |f (x - y) - f x| * |K N y| ≤
      2 * C * (∫ y in (-π)..(-δ'), |K N y|) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hneg_π_le_neg_δ' hdiff_sub_1 (habs_sub_1.const_mul _)
    intro y _
    exact mul_le_mul_of_nonneg_right
      (by calc |f (x - y) - f x| ≤ |f (x - y)| + |f x| := abs_sub _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring) (abs_nonneg _)
  have h_far2 : ∫ y in δ'..π, |f (x - y) - f x| * |K N y| ≤
      2 * C * (∫ y in δ'..π, |K N y|) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hδ'_le_π hdiff_sub_3 (habs_sub_3.const_mul _)
    intro y _
    exact mul_le_mul_of_nonneg_right
      (by calc |f (x - y) - f x| ≤ |f (x - y)| + |f x| := abs_sub _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring) (abs_nonneg _)
  have htail_N := htail N hN
  have htail_bound : 2 * C * ((∫ y in (-π)..(-δ'), |K N y|) + ∫ y in δ'..π, |K N y|) ≤
      2 * C * (ε * π / (2 * C + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt htail_N) (by positivity)
  calc 1 / (2 * π) * |∫ y in (-π)..π, (f (x - y) - f x) * K N y|
      _ ≤ 1 / (2 * π) * ∫ y in (-π)..π, |(f (x - y) - f x) * K N y| := by
          exact mul_le_mul_of_nonneg_left hnorm_le (by positivity)
      _ = 1 / (2 * π) * ((∫ y in (-π)..(-δ'), |(f (x - y) - f x) * K N y|)
          + (∫ y in (-δ')..δ', |(f (x - y) - f x) * K N y|)
          + ∫ y in δ'..π, |(f (x - y) - f x) * K N y|) := by rw [h_split]
      _ = 1 / (2 * π) * ((∫ y in (-π)..(-δ'), |f (x - y) - f x| * |K N y|)
          + (∫ y in (-δ')..δ', |f (x - y) - f x| * |K N y|)
          + ∫ y in δ'..π, |f (x - y) - f x| * |K N y|) := by simp_rw [abs_mul]
      _ ≤ 1 / (2 * π) * (2 * C * (∫ y in (-π)..(-δ'), |K N y|)
          + ε * π / (M + 1) * M
          + 2 * C * (∫ y in δ'..π, |K N y|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h_near_bound := h_near.trans (mul_le_mul_of_nonneg_left h_near_K_le (by positivity))
          linarith [h_far1, h_far2, h_near_bound]
      _ = 1 / (2 * π) * (ε * π / (M + 1) * M
          + 2 * C * ((∫ y in (-π)..(-δ'), |K N y|) + ∫ y in δ'..π, |K N y|)) := by ring
      _ ≤ 1 / (2 * π) * (ε * π / (M + 1) * M
          + 2 * C * (ε * π / (2 * C + 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [htail_bound]
      _ ≤ ε := by
          have h1 : 0 < M + 1 := by linarith
          have h2 : 0 < 2 * C + 1 := by linarith
          have key : ε * π / (M + 1) * M + 2 * C * (ε * π / (2 * C + 1)) =
              ε * π * (M / (M + 1) + 2 * C / (2 * C + 1)) := by field_simp
          rw [key]
          calc 1 / (2 * π) * (ε * π * (M / (M + 1) + 2 * C / (2 * C + 1)))
              ≤ 1 / (2 * π) * (ε * π * 2) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                linarith [show M / (M + 1) ≤ 1 from by rw [div_le_one h1]; linarith,
                          show 2 * C / (2 * C + 1) ≤ 1 from by rw [div_le_one h2]; linarith]
            _ = ε := by field_simp

noncomputable def fejerKernel (N : ℕ) (x : ℝ) : ℝ :=
  if N = 0 then 0
  else if sin (x / 2) = 0 then (N : ℝ)
  else (1 / N : ℝ) * (sin (N * x / 2) / sin (x / 2)) ^ 2

lemma abs_sin_mul_le (n : ℕ) (θ : ℝ) : |sin (n * θ)| ≤ n * |sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, sin_add]
    calc |sin (↑n * θ) * cos θ + cos (↑n * θ) * sin θ|
        ≤ |sin (↑n * θ)| * |cos θ| + |cos (↑n * θ)| * |sin θ| := by
          exact le_trans (abs_add_le _ _) (by rw [abs_mul, abs_mul])
      _ ≤ ↑n * |sin θ| * 1 + 1 * |sin θ| := by
          linarith [mul_le_mul ih (abs_cos_le_one θ) (abs_nonneg _)
                      (by positivity : 0 ≤ ↑n * |sin θ|),
                     mul_le_mul_of_nonneg_right (abs_cos_le_one (↑n * θ)) (abs_nonneg (sin θ))]
      _ = (↑n + 1) * |sin θ| := by ring

lemma fejerKernel_measurable (N : ℕ) : Measurable (fejerKernel N) := by
  unfold fejerKernel
  by_cases hN : N = 0
  · simp [hN]
  · simp only [hN, ↓reduceIte]
    apply Measurable.ite
    · exact (isClosed_eq (continuous_sin.comp (continuous_id.div_const 2))
        continuous_const).measurableSet
    · exact measurable_const
    · exact ((measurable_sin.comp ((measurable_const.mul measurable_id).div_const 2)).div
        (measurable_sin.comp (measurable_id.div_const 2))).pow measurable_const
        |>.const_mul _

lemma fejerKernel_nonneg_aux (N : ℕ) (x : ℝ) : 0 ≤ fejerKernel N x := by
  unfold fejerKernel
  split_ifs <;> [exact le_refl 0; exact Nat.cast_nonneg N;
    exact mul_nonneg (by positivity) (sq_nonneg _)]

lemma fejerKernel_le_N (N : ℕ) (x : ℝ) : fejerKernel N x ≤ N := by
  unfold fejerKernel
  split_ifs with h0 hs
  · simp [h0]
  · exact le_refl _
  · have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero h0
    have key : |sin (↑N * x / 2) / sin (x / 2)| ≤ N := by
      rw [abs_div, div_le_iff₀ (abs_pos.mpr hs)]
      rw [show ↑N * x / 2 = ↑N * (x / 2) from by ring]
      exact abs_sin_mul_le N (x / 2)
    have hbound : (sin (↑N * x / 2) / sin (x / 2)) ^ 2 ≤ (↑N) ^ 2 := by
      rw [← sq_abs (sin (↑N * x / 2) / sin (x / 2))]
      exact pow_le_pow_left₀ (abs_nonneg _) key 2
    calc (1 / ↑N) * (sin (↑N * x / 2) / sin (x / 2)) ^ 2
        ≤ (1 / ↑N) * ↑N ^ 2 :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ↑N := by field_simp

lemma fejerKernel_intervalIntegrable (N : ℕ) :
    IntervalIntegrable (fejerKernel N) volume (-π) π := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [pi_pos])]
  apply Measure.integrableOn_of_bounded
  · exact measure_Ioc_lt_top.ne
  · exact (fejerKernel_measurable N).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux N x)]
    exact fejerKernel_le_N N x

lemma integral_cos_nat_mul_eq_zero (k : ℕ) (hk : k ≠ 0) :
    ∫ x in (-π)..π, cos (↑k * x) = 0 := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have : (fun x => cos (↑k * x)) = (fun x => cos (x * ↑k)) := by ext x; rw [mul_comm]
  rw [this, integral_comp_mul_right cos hk_ne, integral_cos, neg_mul, sin_neg]
  have h_sin : sin (π * ↑k) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi k
  simp [h_sin]

lemma integral_const_mul_cos_eq_zero (c : ℝ) (k : ℕ) :
    ∫ x in (-π)..π, c * cos ((↑k + 1) * x) = 0 := by
  rw [show (fun x => c * cos ((↑k + 1) * x)) = (fun x => c * cos (↑(k + 1) * x)) from by
    ext x; push_cast; ring]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_cos_nat_mul_eq_zero (k + 1) (by omega)]
  simp

lemma two_sin_half_mul_cos (k : ℕ) (x : ℝ) :
    2 * sin (x / 2) * cos (↑k * x) =
      sin ((2 * ↑k + 1) * (x / 2)) - sin ((2 * ↑k - 1) * (x / 2)) := by
  have h1 : sin ((2 * ↑k + 1) * (x / 2)) = sin (↑k * x + x / 2) := by ring_nf
  have h2 : sin ((2 * ↑k - 1) * (x / 2)) = sin (↑k * x - x / 2) := by ring_nf
  rw [h1, h2, sin_add, sin_sub]; ring

lemma dirichlet_identity (n : ℕ) (x : ℝ) :
    sin ((2 * ↑n + 1) * (x / 2)) =
      sin (x / 2) + 2 * sin (x / 2) * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ← add_assoc, ← ih]
    push_cast
    have h := two_sin_half_mul_cos (m + 1) x
    push_cast at h
    have key : (2 * (↑m + 1) - 1 : ℝ) = 2 * ↑m + 1 := by ring
    rw [key] at h
    linarith

lemma fejer_telescope (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range N, sin ((2 * ↑n + 1) * (x / 2)) * sin (x / 2) =
      sin (↑N * x / 2) ^ 2 := by
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]; push_cast
    have h_prod : 2 * sin ((2 * ↑m + 1) * (x / 2)) * sin (x / 2) =
        cos (↑m * x) - cos ((↑m + 1) * x) := by
      have := cos_sub_cos (↑m * x) ((↑m + 1) * x)
      have h1 : (↑m * x + (↑m + 1) * x) / 2 = (2 * ↑m + 1) * (x / 2) := by ring
      have h2 : (↑m * x - (↑m + 1) * x) / 2 = -(x / 2) := by ring
      rw [h1, h2, sin_neg] at this; linarith
    have h_cos1 : cos (↑m * x) = 1 - 2 * sin (↑m * x / 2) ^ 2 := by
      rw [show ↑m * x = 2 * (↑m * x / 2) from by ring, cos_two_mul, sin_sq]; ring_nf
    have h_cos2 : cos ((↑m + 1) * x) = 1 - 2 * sin ((↑m + 1) * x / 2) ^ 2 := by
      rw [show (↑m + 1) * x = 2 * ((↑m + 1) * x / 2) from by ring, cos_two_mul, sin_sq]; ring_nf
    nlinarith

lemma sin_half_ne_zero_of_ne_zero {x : ℝ} (hx : x ∈ Ioc (-π) π) (hx0 : x ≠ 0) :
    sin (x / 2) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h
  have hx_eq : x = 2 * ↑n * π := by linarith
  have hpi := pi_pos
  have h1 : -(1 : ℤ) < 2 * n := by
    by_contra hc; rw [not_lt] at hc
    have : (2 * (n : ℝ)) ≤ -1 := by exact_mod_cast hc
    nlinarith [hx.1]
  have h2 : 2 * n ≤ (1 : ℤ) := by
    by_contra hc; rw [not_le] at hc
    have : (2 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hc
    nlinarith [hx.2]
  exact hx0 (by rw [hx_eq]; simp [show n = 0 from by omega])

lemma integral_dirichlet_sum (n : ℕ) :
    ∫ x in (-π)..π, (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) = 2 * π := by
  induction n with
  | zero => simp [intervalIntegral.integral_const, smul_eq_mul]; ring
  | succ m ih =>
    have h_rw : (fun x => 1 + 2 * ∑ k ∈ Finset.range (m + 1), cos ((↑k + 1) * x)) =
      (fun x => (1 + 2 * ∑ k ∈ Finset.range m, cos ((↑k + 1) * x)) +
        2 * cos ((↑m + 1) * x)) := by
      ext x; rw [Finset.sum_range_succ]; ring
    rw [h_rw, intervalIntegral.integral_add]
    · rw [integral_const_mul_cos_eq_zero 2 m, add_zero, ih]
    · exact (Continuous.add continuous_const (Continuous.mul continuous_const
        (continuous_finsetSum _ (fun k _ =>
          continuous_cos.comp (continuous_const.mul continuous_id))))).intervalIntegrable _ _
    · exact ((continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _).const_mul _

lemma integral_fejer_sum_all (N : ℕ) :
    ∫ x in (-π)..π, ∑ n ∈ Finset.range N,
      (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) = ↑N * (2 * π) := by
  induction N with
  | zero => simp
  | succ m ih =>
    have h_rw : (fun x => ∑ n ∈ Finset.range (m + 1),
        (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x))) =
      fun x => (∑ n ∈ Finset.range m,
        (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x))) +
        (1 + 2 * ∑ k ∈ Finset.range m, cos ((↑k + 1) * x)) := by
      ext x; rw [Finset.sum_range_succ]
    have h_cts : ∀ n : ℕ, Continuous (fun x =>
        (1 : ℝ) + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) :=
      fun n => Continuous.add continuous_const (Continuous.mul continuous_const
        (continuous_finsetSum _ (fun k _ =>
          continuous_cos.comp (continuous_const.mul continuous_id))))
    rw [h_rw, intervalIntegral.integral_add
      ((continuous_finsetSum _ (fun n _ => h_cts n)).intervalIntegrable _ _)
      ((h_cts m).intervalIntegrable _ _)]
    rw [ih, integral_dirichlet_sum]; push_cast; ring

theorem fejerKernel_normalize (N : ℕ) (hN : N ≠ 0) :
    (1 / (2 * π)) * ∫ x in (-π)..π, fejerKernel N x = 1 := by
  have h_ae : ∀ᵐ (x : ℝ) ∂volume, x ∈ uIoc (-π) π →
      fejerKernel N x = (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
        (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) := by
    have h_ne : ∀ᵐ (x : ℝ) ∂volume, x ≠ 0 := by
      rw [Filter.eventually_iff, mem_ae_iff]
      change volume {x : ℝ | ¬x ≠ 0} = 0
      have : {x : ℝ | ¬x ≠ 0} = {(0 : ℝ)} := by ext x; simp
      rw [this]; exact Real.volume_singleton
    filter_upwards [h_ne] with x hx0 hx_mem
    have hx' : x ∈ Ioc (-π) π := by rwa [uIoc_of_le (by linarith [pi_pos])] at hx_mem
    have hsin : sin (x / 2) ≠ 0 := sin_half_ne_zero_of_ne_zero hx' hx0
    unfold fejerKernel; simp only [hN, hsin, ↓reduceIte]
    congr 1
    rw [div_pow, ← fejer_telescope N x, Finset.sum_div]
    congr 1; ext n
    rw [dirichlet_identity n x]; field_simp
  rw [integral_congr_ae h_ae, intervalIntegral.integral_const_mul, integral_fejer_sum_all N]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hpi : π ≠ 0 := ne_of_gt pi_pos
  field_simp

noncomputable instance : Fact (0 < (2 * π : ℝ)) := ⟨by positivity⟩

theorem fejer_uniform_convergence (g : ℝ → ℝ)
    (hg_cont : Continuous g) (hg_per : Function.Periodic g (2 * π)) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ℝ,
      |g x - periodicConvolution g (fejerKernel N) x| ≤ ε := by
  suffices key : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x : ℝ,
      |g x - periodicConvolution g (fejerKernel (n + 1)) x| ≤ ε by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := key ε hε
    exact ⟨N₀ + 1, fun N hN x => by
      have : N = (N - 1) + 1 := by omega
      rw [this]; exact hN₀ (N - 1) (by omega) x⟩
  apply approximate_identity_lemma g (fun n => fejerKernel (n + 1)) hg_cont hg_per
  · intro N; exact fejerKernel_intervalIntegrable (N + 1)
  · intro N x
    exact (fejerKernel_intervalIntegrable (N + 1)).continuousOn_mul
      ((hg_cont.comp (continuous_const.sub continuous_id)).continuousOn)
  · intro N
    have : (fun y => |fejerKernel (N + 1) y|) = fejerKernel (N + 1) := by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (N + 1) y)]
    rw [this]; exact fejerKernel_intervalIntegrable (N + 1)
  · intro N x
    have h_eq : (fun y => |g (x - y) - g x| * |fejerKernel (N + 1) y|) =
        fun y => |g (x - y) - g x| * fejerKernel (N + 1) y := by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (N + 1) y)]
    rw [h_eq]
    exact (fejerKernel_intervalIntegrable (N + 1)).continuousOn_mul
      ((hg_cont.comp (continuous_const.sub continuous_id)).sub continuous_const).abs.continuousOn
  · intro N; exact fejerKernel_normalize (N + 1) (Nat.succ_ne_zero N)
  · refine ⟨2 * π, fun N => ?_⟩
    have hab : (fun y => |fejerKernel (N + 1) y|) = fejerKernel (N + 1) := by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (N + 1) y)]
    rw [hab]
    have h_norm := fejerKernel_normalize (N + 1) (Nat.succ_ne_zero N)
    have hI : ∫ x in (-π)..π, fejerKernel (N + 1) x = 2 * π := by
      have : (0 : ℝ) < 2 * π := by positivity
      field_simp at h_norm; linarith
    linarith
  · intro δ hδ_pos hδ_le_pi
    have hpi_pos := pi_pos
    have hδ2_pos : 0 < δ / 2 := by linarith
    have hδ2_lt_pi : δ / 2 < π := by linarith
    have hsin_δ_pos : 0 < sin (δ / 2) := sin_pos_of_pos_of_lt_pi hδ2_pos hδ2_lt_pi
    have hsin_δ_sq_pos : 0 < sin (δ / 2) ^ 2 := sq_pos_of_pos hsin_δ_pos
    have h_abs_eq : ∀ n, (fun x => |fejerKernel (n + 1) x|) = fejerKernel (n + 1) := fun n => by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (n + 1) y)]
    simp_rw [h_abs_eq]
    set C : ℕ → ℝ := fun n => 1 / ((n + 1 : ℝ) * sin (δ / 2) ^ 2) with hC_def
    have h_pw_pos : ∀ n, ∀ x ∈ Icc δ π, fejerKernel (n + 1) x ≤ C n := by
      intro n x ⟨hxl, hxr⟩
      have hx_half_pos : 0 < x / 2 := by linarith [lt_of_lt_of_le hδ_pos hxl]
      have hx_half_le : x / 2 ≤ π / 2 := by linarith
      have hsin_x_pos : 0 < sin (x / 2) := sin_pos_of_pos_of_lt_pi hx_half_pos (by linarith)
      have hsin_x_ne : sin (x / 2) ≠ 0 := ne_of_gt hsin_x_pos
      have hsin_mono : sin (δ / 2) ≤ sin (x / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx_half_le (by linarith)
      have hsq_mono : sin (δ / 2) ^ 2 ≤ sin (x / 2) ^ 2 :=
        sq_le_sq' (by linarith [sin_nonneg_of_nonneg_of_le_pi hδ2_pos.le (by linarith : δ / 2 ≤ π)])
          hsin_mono
      unfold fejerKernel
      simp only [Nat.succ_ne_zero, hsin_x_ne, ↓reduceIte, div_pow]
      have hN_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      simp only [Nat.cast_add, Nat.cast_one] at *
      calc 1 / ((n : ℝ) + 1) * (sin (((n : ℝ) + 1) * x / 2) ^ 2 / sin (x / 2) ^ 2)
          ≤ 1 / ((n : ℝ) + 1) * (1 / sin (x / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right (sin_sq_le_one _) (sq_pos_of_ne_zero hsin_x_ne).le
        _ ≤ 1 / ((n : ℝ) + 1) * (1 / sin (δ / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq_mono
        _ = C n := by simp only [hC_def]; field_simp
    have h_pw_neg : ∀ n, ∀ x ∈ Icc (-π) (-δ), fejerKernel (n + 1) x ≤ C n := by
      intro n x ⟨hxl, hxr⟩
      have hnx_pos : 0 < -x / 2 := by linarith
      have hnx_le : -x / 2 ≤ π / 2 := by linarith
      have hsin_nx_pos : 0 < sin (-x / 2) := sin_pos_of_pos_of_lt_pi hnx_pos (by linarith)
      have hsin_sq : sin (x / 2) ^ 2 = sin (-x / 2) ^ 2 := by
        rw [show -x / 2 = -(x / 2) from by ring, sin_neg]; ring
      have hsin_x_ne : sin (x / 2) ≠ 0 := by
        intro h; have := sq_eq_zero_iff.mpr h; rw [hsin_sq] at this
        linarith [sq_pos_of_pos hsin_nx_pos]
      have hsin_mono : sin (δ / 2) ≤ sin (-x / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) hnx_le (by linarith)
      have hsq_mono : sin (δ / 2) ^ 2 ≤ sin (x / 2) ^ 2 := by
        rw [hsin_sq]
        have hsin_nn := sin_nonneg_of_nonneg_of_le_pi hδ2_pos.le (by linarith : δ / 2 ≤ π)
        exact sq_le_sq' (by linarith) hsin_mono
      unfold fejerKernel
      simp only [Nat.succ_ne_zero, hsin_x_ne, ↓reduceIte, div_pow]
      simp only [Nat.cast_add, Nat.cast_one] at *
      calc 1 / ((n : ℝ) + 1) * (sin (((n : ℝ) + 1) * x / 2) ^ 2 / sin (x / 2) ^ 2)
          ≤ 1 / ((n : ℝ) + 1) * (1 / sin (x / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right (sin_sq_le_one _) (sq_pos_of_ne_zero hsin_x_ne).le
        _ ≤ 1 / ((n : ℝ) + 1) * (1 / sin (δ / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq_mono
        _ = C n := by simp only [hC_def]; field_simp
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * (π - δ) / (ε * sin (δ / 2) ^ 2))
    use N₀
    intro n hn
    rw [Real.dist_eq, sub_zero]
    have hsum_nonneg : 0 ≤ (∫ x in (-π)..(-δ), fejerKernel (n + 1) x) +
        ∫ x in δ..π, fejerKernel (n + 1) x := by
      apply add_nonneg
      · exact intervalIntegral.integral_nonneg (by linarith)
          (fun u _ => fejerKernel_nonneg_aux (n+1) u)
      · exact intervalIntegral.integral_nonneg hδ_le_pi (fun u _ => fejerKernel_nonneg_aux (n+1) u)
    rw [abs_of_nonneg hsum_nonneg]
    have hC_bound : C n ≥ 0 := by simp only [hC_def]; positivity
    have h_bound_neg : ‖∫ x in (-π)..(-δ), fejerKernel (n + 1) x‖ ≤ C n * |(-δ) - (-π)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux (n+1) x)]
      apply h_pw_neg n x
      rw [uIoc_of_le (by linarith : -π ≤ -δ)] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have h_bound_pos : ‖∫ x in δ..π, fejerKernel (n + 1) x‖ ≤ C n * |π - δ| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux (n+1) x)]
      apply h_pw_pos n x
      rw [uIoc_of_le hδ_le_pi] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have habs_neg : |-δ - -π| = π - δ := by
      rw [show -δ - -π = π - δ from by ring]; exact abs_of_nonneg (by linarith)
    have habs_pos : |π - δ| = π - δ := abs_of_nonneg (by linarith)
    rw [habs_neg] at h_bound_neg; rw [habs_pos] at h_bound_pos
    have h_neg_le : ∫ x in (-π)..(-δ), fejerKernel (n + 1) x ≤ C n * (π - δ) := by
      rwa [Real.norm_eq_abs, abs_of_nonneg
        (intervalIntegral.integral_nonneg (by linarith)
          (fun u _ => fejerKernel_nonneg_aux (n+1) u))] at h_bound_neg
    have h_pos_le : ∫ x in δ..π, fejerKernel (n + 1) x ≤ C n * (π - δ) := by
      rwa [Real.norm_eq_abs, abs_of_nonneg
        (intervalIntegral.integral_nonneg hδ_le_pi
          (fun u _ => fejerKernel_nonneg_aux (n+1) u))] at h_bound_pos
    have hN_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc (∫ x in (-π)..(-δ), fejerKernel (n + 1) x) + ∫ x in δ..π, fejerKernel (n + 1) x
        ≤ C n * (π - δ) + C n * (π - δ) := add_le_add h_neg_le h_pos_le
      _ = 2 * (π - δ) * C n := by ring
      _ = 2 * (π - δ) / (((n : ℝ) + 1) * sin (δ / 2) ^ 2) := by simp only [hC_def]; ring
      _ < ε := by
          rw [div_lt_iff₀ (mul_pos hN_pos hsin_δ_sq_pos)]
          have hes := mul_pos hε hsin_δ_sq_pos
          have h1 : 2 * (π - δ) < ↑N₀ * (ε * sin (δ / 2) ^ 2) := by
            rwa [div_lt_iff₀ hes] at hN₀
          have h2 : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have h3 : ↑N₀ * (ε * sin (δ / 2) ^ 2) ≤ ↑n * (ε * sin (δ / 2) ^ 2) :=
            mul_le_mul_of_nonneg_right h2 hes.le
          nlinarith

lemma cos_eq_one_of_sin_half_eq_zero (x : ℝ) (h : sin (x / 2) = 0) (n : ℕ) :
    cos (n * x) = 1 := by
  rw [sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hx : x = 2 * k * π := by linarith
  rw [hx, show (n : ℝ) * (2 * ↑k * π) = ↑(n * k) * (2 * π) from by push_cast; ring]
  exact cos_int_mul_two_pi (n * k)

private lemma sum_odd_eq_sq (N : ℕ) :
    ∑ j ∈ Finset.range N, ((1 : ℝ) + 2 * j) = N ^ 2 := by
  induction N with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma fejerKernel_eq_dirichlet_avg (N : ℕ) (hN : N ≠ 0) (x : ℝ) :
    fejerKernel N x =
      (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
        (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) := by
  by_cases hsin : sin (x / 2) = 0
  · unfold fejerKernel; simp only [hN, hsin, ↓reduceIte]
    have h1 : ∀ k : ℕ, cos ((↑k + 1) * x) = 1 := fun k => by
      have := cos_eq_one_of_sin_half_eq_zero x hsin (k + 1)
      convert this using 1; push_cast; ring
    simp_rw [h1, Finset.sum_const, Finset.card_range, Nat.smul_one_eq_cast]
    rw [sum_odd_eq_sq]
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    field_simp
  · unfold fejerKernel; simp only [hN, hsin, ↓reduceIte]
    congr 1
    have hdir : ∀ (j : ℕ), sin ((2 * ↑j + 1) * (x / 2)) * sin (x / 2) =
        sin (x / 2) ^ 2 * (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) := by
      intro j; rw [dirichlet_identity j x]; ring
    have htel := fejer_telescope N x
    have hsum : sin (x / 2) ^ 2 * ∑ j ∈ Finset.range N,
        (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) = sin (↑N * x / 2) ^ 2 := by
      rw [Finset.mul_sum]
      have : ∀ i ∈ Finset.range N,
          sin (x / 2) ^ 2 * (1 + 2 * ∑ k ∈ Finset.range i, cos ((↑k + 1) * x)) =
          sin ((2 * ↑i + 1) * (x / 2)) * sin (x / 2) :=
        fun i _ => (hdir i).symm
      rw [Finset.sum_congr rfl this]
      exact htel
    have hsin2 : sin (x / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hsin
    rw [div_pow]
    have hsin2_pos : (0 : ℝ) < sin (x / 2) ^ 2 := by positivity
    rw [div_eq_iff (ne_of_gt hsin2_pos)]
    linarith

/-- The Dirichlet kernel `D_N(y) = 1 + 2 ∑_{k=1}^{N} cos(k y)`. -/
noncomputable def dirichletKernel (N : ℕ) (y : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ Finset.range N, Real.cos ((k + 1) * y)

lemma Icc_neg_succ (m : ℕ) :
    Finset.Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) =
      insert (-((m + 1 : ℕ) : ℤ)) (insert ((m + 1 : ℕ) : ℤ) (Finset.Icc (-(m : ℤ)) m)) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_insert]
  push_cast
  omega

/-- `∑_{|n| ≤ N} e^{iny} = D_N(y)`. -/
lemma sum_exp_eq_dirichletKernel (N : ℕ) (y : ℝ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, Complex.exp (Complex.I * n * y) = (dirichletKernel N y : ℂ) := by
  induction N with
  | zero => simp [dirichletKernel]
  | succ m ih =>
    rw [Icc_neg_succ, Finset.sum_insert, Finset.sum_insert, ih]
    · have h : Complex.exp (Complex.I * (-((m : ℂ) + 1)) * y) +
          Complex.exp (Complex.I * ((m : ℂ) + 1) * y) = 2 * Complex.cos (((m : ℂ) + 1) * y) := by
        rw [Complex.two_cos]; ring_nf
      simp only [dirichletKernel, Finset.sum_range_succ]
      push_cast
      linear_combination h
    · simp only [Finset.mem_Icc]; push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega

/-- `D_N` is `2π`-periodic. -/
lemma dirichletKernel_periodic (N : ℕ) : Function.Periodic (dirichletKernel N) (2 * π) := by
  intro y
  simp only [dirichletKernel]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show ((k : ℝ) + 1) * (y + 2 * π) = ((k : ℝ) + 1) * y + ((k + 1 : ℕ) : ℤ) * (2 * π) by
    push_cast; ring]
  exact Real.cos_add_int_mul_two_pi _ _

/-- `fourier (-n)` on `AddCircle (2π - 0)` at a real point is `e^{-int}`. -/
lemma fourier_neg_coe_two_pi (n : ℤ) (t : ℝ) :
    fourier (-n) (t : AddCircle (2 * π - 0)) = Complex.exp (-(Complex.I * n * t)) := by
  rw [fourier_coe_apply]
  congr 1
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- The symmetric Fourier partial sum of a continuous `2π`-periodic function is its
convolution with the Dirichlet kernel. -/
lemma partialSum_eq_integral_dirichletKernel {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hcont : Continuous f) (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        fourierCoeffOn Real.two_pi_pos f n * Complex.exp (Complex.I * n * x) =
      (1 / (2 * π) : ℂ) * ∫ y in (-π)..π, f (x - y) * dirichletKernel N y := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  -- Each term is an integral over `[0, 2π]`.
  have hterm : ∀ n : ℤ, fourierCoeffOn Real.two_pi_pos f n * Complex.exp (Complex.I * n * x) =
      (1 / (2 * π) : ℂ) * ∫ t in (0 : ℝ)..2 * π, f t * Complex.exp (Complex.I * n * (x - t)) := by
    intro n
    rw [fourierCoeffOn_eq_integral]
    simp_rw [fourier_neg_coe_two_pi, smul_eq_mul]
    rw [sub_zero, Complex.real_smul]
    rw [mul_assoc, ← intervalIntegral.integral_mul_const]
    push_cast
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mul_comm (Complex.exp _) (f t), mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum]
  swap
  · intro n _
    exact (hcont.mul (by fun_prop)).intervalIntegrable _ _
  congr 1
  simp_rw [← Finset.mul_sum]
  -- `∑ e^{in(x - t)} = D_N(x - t)`, then substitute `y = x - t` and shift by a period.
  have hsum : ∀ t : ℝ, ∑ n ∈ Finset.Icc (-(N : ℤ)) N, Complex.exp (Complex.I * n * (x - t)) =
      (dirichletKernel N (x - t) : ℂ) := fun t => by
    rw [← sum_exp_eq_dirichletKernel N (x - t)]
    push_cast
    rfl
  simp_rw [hsum]
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun y : ℝ => f (x - y) * (dirichletKernel N y : ℂ)) (a := 0) (b := 2 * π) x
  simp only [sub_sub_cancel] at hsub
  rw [hsub]
  have hg : Function.Periodic (fun y : ℝ => f (x - y) * (dirichletKernel N y : ℂ)) (2 * π) := by
    intro y
    simp only
    rw [dirichletKernel_periodic N y, show x - (y + 2 * π) = x - y - 2 * π by ring, hper.sub_eq]
  have := hg.intervalIntegral_add_eq (x - 2 * π) (-π)
  simp only [sub_add_cancel, show -π + 2 * π = π by ring] at this
  rw [sub_zero, this]

/-- The Fejér kernel `F_{N+1}` is the average of the Dirichlet kernels `D_0, …, D_N`. -/
lemma fejerKernel_succ_eq_avg (N : ℕ) (y : ℝ) :
    fejerKernel (N + 1) y =
      (1 / ((N : ℝ) + 1)) * ∑ k ∈ Finset.range (N + 1), dirichletKernel k y := by
  rw [fejerKernel_eq_dirichlet_avg (N + 1) (Nat.succ_ne_zero N)]
  push_cast
  rfl

lemma continuous_dirichletKernel (N : ℕ) : Continuous (dirichletKernel N) := by
  unfold dirichletKernel; fun_prop

/-- The Cesàro mean of the first `N + 1` symmetric partial sums is the convolution with
`F_{N+1}`. -/
lemma cesaroMean_eq_integral_fejerKernel {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hcont : Continuous f) (N : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (N + 1), ∑ n ∈ Finset.Icc (-(k : ℤ)) k,
        fourierCoeffOn Real.two_pi_pos f n * Complex.exp (Complex.I * n * x)) / (N + 1 : ℂ) =
      (1 / (2 * π) : ℂ) * ∫ y in (-π)..π, f (x - y) * fejerKernel (N + 1) y := by
  simp_rw [partialSum_eq_integral_dirichletKernel hper hcont, ← Finset.mul_sum]
  have hk : ∀ k ∈ Finset.range (N + 1), IntervalIntegrable
      (fun y => f (x - y) * (dirichletKernel k y : ℂ)) volume (-π) π := fun k _ =>
    ((hcont.comp (continuous_const.sub continuous_id)).mul
      (Complex.continuous_ofReal.comp (continuous_dirichletKernel k))).intervalIntegrable _ _
  rw [← intervalIntegral.integral_finsetSum hk]
  have hint : ∀ y : ℝ, f (x - y) * (fejerKernel (N + 1) y : ℂ) =
      (1 / ((N : ℂ) + 1)) * ∑ k ∈ Finset.range (N + 1), f (x - y) * (dirichletKernel k y : ℂ) := by
    intro y
    rw [fejerKernel_succ_eq_avg, ← Finset.mul_sum]
    push_cast
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_const_mul]
  have hN : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
  field_simp

/-- The symmetric Fourier partial sum of `f : ℝ → ℂ` on the period `[0, 2π]`:
`S_N(f)(x) = ∑_{n = -N}^{N} f̂_n · e^{inx}`, with `f̂_n = fourierCoeffOn _ f n`. -/
@[expose] public noncomputable def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    fourierCoeffOn Real.two_pi_pos f n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))

/-- The Cesàro mean of the first `N + 1` Fourier partial sums:
`σ_N(f)(x) = (S_0(f)(x) + S_1(f)(x) + ⋯ + S_N(f)(x)) / (N + 1)`. -/
@[expose] public noncomputable def fourierCesaroMean (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ k ∈ Finset.range (N + 1), fourierPartialSum f k x) / (N + 1 : ℂ)

/-- With `F = F_{N+1}` real, the Cesàro mean splits into the convolutions of `Re f` and `Im f`. -/
lemma fourierCesaroMean_eq {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) (hcont : Continuous f)
    (N : ℕ) (x : ℝ) :
    fourierCesaroMean f N x =
      (periodicConvolution (fun t => (f t).re) (fejerKernel (N + 1)) x : ℂ) +
        Complex.I * (periodicConvolution (fun t => (f t).im) (fejerKernel (N + 1)) x : ℂ) := by
  have hF := fejerKernel_intervalIntegrable (N + 1)
  have hre : IntervalIntegrable (fun y => (f (x - y)).re * fejerKernel (N + 1) y) volume (-π) π :=
    hF.continuousOn_mul ((Complex.continuous_re.comp (hcont.comp
      (continuous_const.sub continuous_id))).continuousOn)
  have him : IntervalIntegrable (fun y => (f (x - y)).im * fejerKernel (N + 1) y) volume (-π) π :=
    hF.continuousOn_mul ((Complex.continuous_im.comp (hcont.comp
      (continuous_const.sub continuous_id))).continuousOn)
  unfold fourierCesaroMean fourierPartialSum
  rw [cesaroMean_eq_integral_fejerKernel hper hcont]
  have hsplit : ∀ y : ℝ, f (x - y) * (fejerKernel (N + 1) y : ℂ) =
      (((f (x - y)).re * fejerKernel (N + 1) y : ℝ) : ℂ) +
        Complex.I * (((f (x - y)).im * fejerKernel (N + 1) y : ℝ) : ℂ) := by
    intro y
    conv_lhs => rw [← Complex.re_add_im (f (x - y))]
    push_cast
    ring
  simp_rw [hsplit]
  have hre' : IntervalIntegrable (fun y => (((f (x - y)).re * fejerKernel (N + 1) y : ℝ) : ℂ))
      volume (-π) π := ⟨hre.1.ofReal, hre.2.ofReal⟩
  have him' : IntervalIntegrable (fun y => (((f (x - y)).im * fejerKernel (N + 1) y : ℝ) : ℂ))
      volume (-π) π := ⟨him.1.ofReal, him.2.ofReal⟩
  rw [intervalIntegral.integral_add hre' (him'.const_mul Complex.I),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  simp only [periodicConvolution]
  push_cast
  ring

/-- **Fejér's theorem**: for a continuous `2π`-periodic `f : ℝ → ℂ`, the Cesàro means of the
symmetric Fourier partial sums converge to `f` uniformly on `ℝ`. -/
public theorem tendstoUniformly_fourierCesaroMean {f : ℝ → ℂ}
    (hperiod : Function.Periodic f (2 * π)) (hcont : Continuous f) :
    TendstoUniformly (fun N : ℕ => fourierCesaroMean f N) f atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hu : Continuous fun t => (f t).re := Complex.continuous_re.comp hcont
  have hv : Continuous fun t => (f t).im := Complex.continuous_im.comp hcont
  have hup : Function.Periodic (fun t => (f t).re) (2 * π) := fun t => by simp [hperiod t]
  have hvp : Function.Periodic (fun t => (f t).im) (2 * π) := fun t => by simp [hperiod t]
  obtain ⟨N₁, h₁⟩ := fejer_uniform_convergence _ hu hup (ε / 3) (by positivity)
  obtain ⟨N₂, h₂⟩ := fejer_uniform_convergence _ hv hvp (ε / 3) (by positivity)
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with N hN x
  have e₁ := h₁ (N + 1) (by omega) x
  have e₂ := h₂ (N + 1) (by omega) x
  rw [dist_eq_norm, fourierCesaroMean_eq hperiod hcont]
  set u := periodicConvolution (fun t => (f t).re) (fejerKernel (N + 1)) x
  set v := periodicConvolution (fun t => (f t).im) (fejerKernel (N + 1)) x
  calc ‖f x - ((u : ℂ) + Complex.I * v)‖
      = ‖(((f x).re - u : ℝ) : ℂ) + Complex.I * (((f x).im - v : ℝ) : ℂ)‖ := by
        congr 1; apply Complex.ext <;> simp
    _ ≤ |(f x).re - u| + |(f x).im - v| := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ ε / 3 + ε / 3 := add_le_add e₁ e₂
    _ < ε := by linarith

end MathlibExt.Analysis.Fourier
