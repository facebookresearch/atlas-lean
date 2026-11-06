/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.AddCircle.CesaroMean
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Fejér's theorem on the additive circle

For every continuous function `f : AddCircle T → ℂ`, the Cesàro–Fourier means
`σ_N f` converge uniformly to `f` (`AddCircle.fejer_uniform_convergence`).
The quantitative form `AddCircle.cesaroMean_uniform_bound` says: given `ε > 0` and
a modulus of continuity `δ > 0` for `f` at scale `ε / 2`, there is `N₀` such that
`∀ N ≥ N₀, ∀ x, dist (f x) (σ_N f x) < ε`. The proof splits the convolution integral
into the region `‖t‖ < δ` (where `f(x) - f(x - t)` is small) and its complement
(where the Fejér kernel decays as `O(1 / ((N + 1) δ²))`).

Source: `v1/Atlas/IntroductionToFunctionalAnalysis/code/FourierSeries.lean`
(target: Theorem (Fejér), April 22, 2021 section). The v1 file used the namespace
`FourierSeries`; here the theorem lives in Mathlib's `AddCircle` namespace.
-/

@[expose] public section

variable {T : ℝ} [hT : Fact (0 < T)]

open MeasureTheory AddCircle Finset Filter Complex

namespace AddCircle

/-- **Quantitative Fejér theorem.** Let $T > 0$, let $f$ be a continuous complex-valued function
on the circle $\mathbb{R}/T\mathbb{Z}$, and write $\sigma_N f$ for its $N$-th Cesàro–Fourier
mean. Let $\varepsilon > 0$ and $\delta > 0$ be such that $|f(a) - f(b)| < \varepsilon / 2$ for
all points $a, b$ of the circle at distance less than $\delta$. Then there is
$N_0 \in \mathbb{N}$ such that $|f(x) - \sigma_N f(x)| < \varepsilon$ for every $N \ge N_0$ and
every point $x$ of the circle.

The proof writes $f(x) - \sigma_N f(x) = \int K_N(t)\,(f(x) - f(x - t))\,dt$, where $K_N$ is the
$N$-th Fejér kernel and the integral is against the Haar probability measure, and splits it
into the points $t$ at distance less than $\delta$ from $0$, where $f(x) - f(x - t)$ is small,
and the remaining points, where the Fejér kernel is $O(1/((N+1)\delta^2))$. -/
theorem cesaroMean_uniform_bound (f : C(AddCircle T, ℂ))
    (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ_pos : 0 < δ)
    (hδ : ∀ ⦃a b : AddCircle T⦄, dist a b < δ → dist (f a) (f b) < ε / 2) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : AddCircle T,
      dist (f x) (cesaroFourierMean (⇑f) N x) < ε := by
  have hf_int : Integrable (⇑f) haarAddCircle :=
    (map_continuous f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcont_norm : Continuous (fun t : AddCircle T => ‖(1 : ℂ) - fourier (1 : ℤ) t‖) :=
    continuous_norm.comp (continuous_const.sub (map_continuous (fourier 1)))
  obtain ⟨δ', hδ'_pos, hδ'_bound⟩ : ∃ δ' : ℝ, 0 < δ' ∧
      ∀ t : AddCircle T, δ ≤ dist t (0 : AddCircle T) →
        δ' ≤ ‖(1 : ℂ) - fourier (1 : ℤ) t‖ := by
    have hS_compact : IsCompact {t : AddCircle T | δ ≤ dist t (0 : AddCircle T)} :=
      (isClosed_le continuous_const (Continuous.dist continuous_id continuous_const)).isCompact
    by_cases hne : ({t : AddCircle T | δ ≤ dist t (0 : AddCircle T)} : Set _).Nonempty
    · obtain ⟨t_min, ht_min_mem, ht_min_le⟩ :=
        hS_compact.exists_isMinOn hne hcont_norm.continuousOn
      refine ⟨‖(1 : ℂ) - fourier (1 : ℤ) t_min‖, ?_, fun t ht => ht_min_le ht⟩
      rw [norm_pos_iff, sub_ne_zero]
      intro h_eq
      have h_dist : dist t_min (0 : AddCircle T) = 0 := by
        have hfourier_eq : (fourier (1 : ℤ) t_min : ℂ) = fourier (1 : ℤ) (0 : AddCircle T) := by
          simp [h_eq.symm]
        have hinj := AddCircle.injective_toCircle (ne_of_gt hT.out)
        have h_val : fourier (1 : ℤ) t_min = fourier (1 : ℤ) (0 : AddCircle T) := by
          exact_mod_cast hfourier_eq
        simp only [fourier_apply, one_zsmul] at h_val
        rw [dist_eq_zero]
        exact hinj (Subtype.coe_injective h_val)
      linarith [show δ ≤ dist t_min (0 : AddCircle T) from ht_min_mem]
    ·
      exact ⟨1, one_pos, fun t ht => absurd ⟨t, ht⟩ hne⟩
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (16 * ‖f‖ / (ε * δ' ^ 2))
  refine ⟨N₀, fun N hN x => ?_⟩
  rw [dist_eq_norm, cesaroMean_eq_fejer_convolution (⇑f) hf_int N x]
  have h_fx_eq : f x = ∫ t : AddCircle T, fejerKernel N t • f x ∂haarAddCircle := by
    have h1 : ∫ t : AddCircle T, fejerKernel N t • f x ∂haarAddCircle =
        (∫ t : AddCircle T, fejerKernel N t ∂haarAddCircle) • f x := integral_smul_const _ (f x)
    rw [h1, integral_fejerKernel, one_smul]
  rw [h_fx_eq]
  have hfx_int : Integrable (fun t : AddCircle T => fejerKernel N t • f x) haarAddCircle :=
    (fejerKernel_integrable N).smul_const (f x)
  have hfxt_int : Integrable (fun t : AddCircle T => fejerKernel N t • f (x - t)) haarAddCircle :=
    (Continuous.smul (fejerKernel_continuous N)
      (f.continuous.comp (continuous_const.sub continuous_id'))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub hfx_int hfxt_int]
  have h_integrand : (fun t => fejerKernel N t • f x - fejerKernel N t • f (x - t)) =
      (fun t => fejerKernel N t • (f x - f (x - t))) := by
    ext t; rw [← smul_sub]
  rw [h_integrand]
  have hN_pos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hδ'_sq_pos : (0 : ℝ) < δ' ^ 2 := by positivity
  have hdecay := (fejer_kernel_properties (T := T) N).2.2.2.2
  set C := 4 / (((N : ℝ) + 1) * δ' ^ 2)
  have hC_nonneg : (0 : ℝ) ≤ C := by positivity
  have h2fC_lt : 2 * ‖f‖ * C < ε / 2 := by
    have hN_ge : (N₀ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
    have hN1 : (N₀ : ℝ) ≤ (N : ℝ) + 1 := by linarith
    have := hN₀
    show 2 * ‖f‖ * (4 / (((N : ℝ) + 1) * δ' ^ 2)) < ε / 2
    by_cases hf_zero : ‖f‖ = 0
    · simp [hf_zero]; linarith
    · have hf_pos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf_zero)
      have h_denom_pos : (0:ℝ) < ((N : ℝ) + 1) * δ' ^ 2 := by positivity
      calc 2 * ‖f‖ * (4 / (((N : ℝ) + 1) * δ' ^ 2))
          = 8 * ‖f‖ / (((N : ℝ) + 1) * δ' ^ 2) := by ring
        _ < ε / 2 := by
          rw [div_lt_iff₀ h_denom_pos]
          have h16 : 16 * ‖f‖ < (↑N + 1) * (ε * δ' ^ 2) := by
            have := mul_lt_mul_of_pos_right (lt_of_lt_of_le hN₀ hN1)
              (show (0:ℝ) < ε * δ' ^ 2 from by positivity)
            rwa [div_mul_cancel₀] at this
            exact ne_of_gt (by positivity : (0:ℝ) < ε * δ' ^ 2)
          linarith
  have hpw : ∀ t : AddCircle T,
      ‖fejerKernel N t • (f x - f (x - t))‖ ≤ ε / 2 * ‖fejerKernel N t‖ + 2 * ‖f‖ * C := by
    intro t
    rw [norm_smul]
    by_cases ht : dist t (0 : AddCircle T) < δ
    ·
      have hfx_close : ‖f x - f (x - t)‖ < ε / 2 := by
        have hd : dist x (x - t) < δ := by
          rw [dist_eq_norm, sub_sub_cancel]
          rwa [dist_eq_norm, sub_zero] at ht
        have := hδ hd
        rwa [dist_eq_norm] at this
      calc ‖fejerKernel N t‖ * ‖f x - f (x - t)‖
          ≤ ‖fejerKernel N t‖ * (ε / 2) := by
            apply mul_le_mul_of_nonneg_left (le_of_lt hfx_close) (norm_nonneg _)
        _ = ε / 2 * ‖fejerKernel N t‖ := by ring
        _ ≤ ε / 2 * ‖fejerKernel N t‖ + 2 * ‖f‖ * C := le_add_of_nonneg_right (by positivity)
    ·
      push Not at ht
      have h_decay_t : ‖fejerKernel N t‖ ≤ C :=
        hdecay δ' hδ'_pos t (hδ'_bound t ht)
      have hf_bound : ‖f x - f (x - t)‖ ≤ 2 * ‖f‖ :=
        calc ‖f x - f (x - t)‖ ≤ ‖f x‖ + ‖f (x - t)‖ := norm_sub_le _ _
          _ ≤ ‖f‖ + ‖f‖ := add_le_add (ContinuousMap.norm_coe_le_norm f x)
              (ContinuousMap.norm_coe_le_norm f (x - t))
          _ = 2 * ‖f‖ := by ring
      calc ‖fejerKernel N t‖ * ‖f x - f (x - t)‖
          ≤ C * (2 * ‖f‖) := mul_le_mul h_decay_t hf_bound (norm_nonneg _) hC_nonneg
        _ = 2 * ‖f‖ * C := by ring
        _ ≤ ε / 2 * ‖fejerKernel N t‖ + 2 * ‖f‖ * C :=
            le_add_of_nonneg_left (by positivity)
  have hg_int : Integrable (fun t : AddCircle T =>
      ε / 2 * ‖fejerKernel N t‖ + 2 * ‖f‖ * C) haarAddCircle := by
    apply Integrable.add
    · exact (fejerKernel_integrable N).norm.const_mul _
    · exact integrable_const _
  calc ‖∫ t : AddCircle T, fejerKernel N t • (f x - f (x - t)) ∂haarAddCircle‖
      ≤ ∫ t : AddCircle T, ‖fejerKernel N t • (f x - f (x - t))‖ ∂haarAddCircle :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t : AddCircle T, (ε / 2 * ‖fejerKernel N t‖ + 2 * ‖f‖ * C) ∂haarAddCircle := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun t => norm_nonneg _)) hg_int
        exact ae_of_all _ hpw
    _ = ε / 2 * (∫ t : AddCircle T, ‖fejerKernel N t‖ ∂haarAddCircle) + 2 * ‖f‖ * C := by
        rw [integral_add ((fejerKernel_integrable N).norm.const_mul _) (integrable_const _)]
        congr 1
        · rw [show (fun t => ε / 2 * ‖fejerKernel N t‖) =
              (fun t => (ε / 2) • ‖fejerKernel N t‖) from by ext; simp [smul_eq_mul]]
          rw [integral_smul]; simp [smul_eq_mul]
        · rw [integral_const]; simp
    _ = ε / 2 + 2 * ‖f‖ * C := by rw [integral_norm_fejerKernel]; ring
    _ < ε := by linarith

/-- **Fejér's theorem: uniform convergence of Cesàro–Fourier means.** Let $T > 0$ and let $f$ be
a continuous complex-valued function on the circle $\mathbb{R}/T\mathbb{Z}$ (equivalently, a
continuous $T$-periodic function on $\mathbb{R}$). Then the Cesàro–Fourier means $\sigma_N f$
converge to $f$ uniformly on the circle as $N \to \infty$. -/
theorem fejer_uniform_convergence (f : C(AddCircle T, ℂ)) :
    TendstoUniformly (fun N => cesaroFourierMean (⇑f) N) (⇑f) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  rw [Filter.eventually_atTop]
  have hf_uc : UniformContinuous (⇑f) :=
    CompactSpace.uniformContinuous_of_continuous f.continuous
  rw [Metric.uniformContinuous_iff] at hf_uc
  obtain ⟨δ, hδ_pos, hδ⟩ := hf_uc (ε / 2) (half_pos hε)
  exact cesaroMean_uniform_bound f ε hε δ hδ_pos hδ

end AddCircle
