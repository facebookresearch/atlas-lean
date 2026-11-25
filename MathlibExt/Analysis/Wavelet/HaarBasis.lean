/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import MathlibExt.Analysis.Wavelet.Haar
import MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

/-!
# The Haar wavelet basis of the real line

The Haar functions at all integer scales and translations form an orthonormal basis of
real `L²(ℝ)` (`exists_hilbertBasis_haarSystem`). The corresponding unit-interval basis, which
includes the constant function, is proved in `MathlibExt.Analysis.Wavelet.HaarBasisUnitInterval`.

## Proof outline

The Haar function `H_{j,k}` is `2^{j/2}` times the difference of the indicators of the two
halves of the dyadic interval `I_{j,k} = [k 2^{-j}, (k + 1) 2^{-j})`, so the family is built in
`L²(ℝ)` from `indicatorConstLp`, and its orthonormality is
`MathlibExt.Analysis.Wavelet.Haar.integral_haarSystem_mul_haarSystem`. For completeness, let
`f ∈ L²(ℝ)` be orthogonal to every `H_{j,k}`. The two halves of each dyadic interval then carry
the same integral of `f`, so the integral of `f` over a dyadic interval is half the integral over
its parent. Going up `n` generations and bounding the integral over the ancestor, of length
`2^{n-j}`, by the Cauchy–Schwarz inequality gives `(∫_{I_{j,k}} f)² ≤ 2^{-n} 2^{-j} ‖f‖²` for
every `n`, so every dyadic integral of `f` vanishes. No constant function is needed: the coarse
scales `j → -∞` take its place. The dyadic Lebesgue differentiation theorem
(`MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal.ae_tendsto_setAverage_dyadicInterval`) then
gives `f = 0` almost everywhere.
-/

public section

open MeasureTheory Set Filter Topology
open MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal

namespace MathlibExt.Analysis.Wavelet.HaarBasisWanted

open MathlibExt.Analysis.Wavelet.Haar

noncomputable section

private lemma mem_dyadicInterval_iff_mul (j m : ℤ) (x : ℝ) :
    x ∈ dyadicInterval j m ↔ (m : ℝ) ≤ 2 ^ j * x ∧ 2 ^ j * x < m + 1 := by
  have h : (0 : ℝ) < 2 ^ j := zpow_pos two_pos j
  simp only [dyadicInterval, mem_Ico, div_le_iff₀ h, lt_div_iff₀ h, mul_comm x]

-- The left half of `I_{j,k}` is where `H_{j,k}` is positive.
private lemma mem_left_half (j k : ℤ) (x : ℝ) :
    x ∈ dyadicInterval (j + 1) (2 * k) ↔ (2 : ℝ) ^ j * x - k ∈ Ico (0 : ℝ) (1 / 2) := by
  rw [mem_dyadicInterval_iff_mul, mem_Ico, zpow_add_one₀ two_ne_zero]
  push_cast
  constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith

-- The right half of `I_{j,k}` is where `H_{j,k}` is negative.
private lemma mem_right_half (j k : ℤ) (x : ℝ) :
    x ∈ dyadicInterval (j + 1) (2 * k + 1) ↔ (2 : ℝ) ^ j * x - k ∈ Ico (1 / 2 : ℝ) 1 := by
  rw [mem_dyadicInterval_iff_mul, mem_Ico, zpow_add_one₀ two_ne_zero]
  push_cast
  constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith

private lemma union_halves (j k : ℤ) :
    dyadicInterval (j + 1) (2 * k) ∪ dyadicInterval (j + 1) (2 * k + 1) =
      dyadicInterval j k := by
  ext x
  rw [mem_union, mem_left_half, mem_right_half, mem_dyadicInterval_iff_mul, mem_Ico, mem_Ico]
  constructor
  · rintro (⟨hl, hr⟩ | ⟨hl, hr⟩) <;> constructor <;> linarith
  · rintro ⟨hl, hr⟩
    by_cases h : (2 : ℝ) ^ j * x - k < 1 / 2
    · exact Or.inl ⟨by linarith, h⟩
    · exact Or.inr ⟨by linarith, by linarith⟩

private lemma disjoint_halves (j k : ℤ) :
    Disjoint (dyadicInterval (j + 1) (2 * k)) (dyadicInterval (j + 1) (2 * k + 1)) := by
  rw [Set.disjoint_left]
  intro x hl hr
  exact ((mem_left_half j k x).1 hl).2.not_ge ((mem_right_half j k x).1 hr).1

-- The indicator of the dyadic interval `I_{j,m}` in `L²(ℝ)`.
private def cellVec (j m : ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  indicatorConstLp 2 (measurableSet_dyadicInterval j m) (volume_dyadicInterval_ne_top j m) 1

-- The Haar function `H_{j,k}` in `L²(ℝ)`, as `2^{j/2}` times the difference of the indicators
-- of the two halves of `I_{j,k}`.
private def haarVec (jk : ℤ × ℤ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (2 : ℝ) ^ ((jk.1 : ℝ) / 2) • (cellVec (jk.1 + 1) (2 * jk.2) - cellVec (jk.1 + 1) (2 * jk.2 + 1))

private lemma cellVec_ae (j m : ℤ) :
    ⇑(cellVec j m) =ᵐ[volume] (dyadicInterval j m).indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

private lemma haarVec_ae (jk : ℤ × ℤ) : ⇑(haarVec jk) =ᵐ[volume] haarSystem jk.1 jk.2 := by
  obtain ⟨j, k⟩ := jk
  unfold haarVec
  filter_upwards [Lp.coeFn_smul ((2 : ℝ) ^ ((j : ℝ) / 2))
      (cellVec (j + 1) (2 * k) - cellVec (j + 1) (2 * k + 1)),
    Lp.coeFn_sub (cellVec (j + 1) (2 * k)) (cellVec (j + 1) (2 * k + 1)),
    cellVec_ae (j + 1) (2 * k), cellVec_ae (j + 1) (2 * k + 1)] with x hsmul hsub hl hr
  simp only [Pi.smul_apply, smul_eq_mul] at hsmul
  simp only [Pi.sub_apply] at hsub
  rw [hsmul, hsub, hl, hr]
  classical
  simp only [haarSystem, haarFunction, Set.indicator, mem_left_half, mem_right_half,
    Pi.one_apply]

private lemma inner_eq_integral_of_ae {v w : Lp ℝ 2 (volume : Measure ℝ)} {f g : ℝ → ℝ}
    (hv : ⇑v =ᵐ[volume] f) (hw : ⇑w =ᵐ[volume] g) :
    inner ℝ v w = ∫ x, f x * g x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv, hw] with x hx hy using by simp [hx, hy, RCLike.inner_apply, mul_comm]

private lemma haarVec_orthonormal : Orthonormal ℝ haarVec := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [inner_eq_integral_of_ae (haarVec_ae a) (haarVec_ae b), integral_haarSystem_mul_haarSystem]

private lemma inner_cellVec (j m : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    inner ℝ (cellVec j m) f = ∫ x in dyadicInterval j m, f x :=
  L2.inner_indicatorConstLp_one _ _ _

-- Cauchy–Schwarz on `I_{j,m}`, which has length `2^{-j}`.
private lemma sq_integral_le_of_level (j m : ℤ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    (∫ x in dyadicInterval j m, f x) ^ 2 ≤ ((2 : ℝ) ^ j)⁻¹ * ‖f‖ ^ 2 := by
  have hnorm : ‖cellVec j m‖ ^ 2 = ((2 : ℝ) ^ j)⁻¹ := by
    have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ j)⁻¹ := by positivity
    rw [cellVec, norm_indicatorConstLp two_ne_zero ENNReal.ofNat_ne_top, norm_one, one_mul,
      measureReal_def, volume_dyadicInterval, ENNReal.toReal_ofReal h0, ENNReal.toReal_ofNat,
      ← Real.sqrt_eq_rpow, Real.sq_sqrt h0]
  rw [← inner_cellVec]
  calc inner ℝ (cellVec j m) f ^ 2 = |inner ℝ (cellVec j m) f| ^ 2 := (sq_abs _).symm
    _ ≤ (‖cellVec j m‖ * ‖f‖) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm _ _) 2
    _ = ((2 : ℝ) ^ j)⁻¹ * ‖f‖ ^ 2 := by rw [mul_pow, hnorm]

-- Orthogonality to `H_{j,q}` splits the integral over `I_{j,q}` evenly between its halves.
private lemma integral_halves (f : Lp ℝ 2 (volume : Measure ℝ))
    (hf : ∀ jk, inner ℝ (haarVec jk) f = 0) (j q : ℤ) :
    ∫ x in dyadicInterval (j + 1) (2 * q), f x = (∫ x in dyadicInterval j q, f x) / 2 ∧
      ∫ x in dyadicInterval (j + 1) (2 * q + 1), f x = (∫ x in dyadicInterval j q, f x) / 2 := by
  have hloc : LocallyIntegrable (⇑f) volume := (Lp.memLp f).locallyIntegrable (by norm_num)
  have hon (i n : ℤ) : IntegrableOn (⇑f) (dyadicInterval i n) :=
    (hloc.integrableOn_isCompact isCompact_Icc).mono_set (by
      rw [dyadicInterval]; exact Ico_subset_Icc_self)
  have hdiff := hf (j, q)
  simp only [haarVec, real_inner_smul_left, inner_sub_left, inner_cellVec] at hdiff
  have hscale : (2 : ℝ) ^ ((j : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
  have heq := sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hscale)
  rw [← union_halves j q, setIntegral_union (disjoint_halves _ _)
    (measurableSet_dyadicInterval _ _) (hon _ _) (hon _ _)]
  constructor <;> linarith

-- Going up `n` generations: `(∫_{I_{j,m}} f)² ≤ 2^{-n} 2^{-j} ‖f‖²`.
private lemma sq_integral_le (f : Lp ℝ 2 (volume : Measure ℝ))
    (hf : ∀ jk, inner ℝ (haarVec jk) f = 0) (n : ℕ) (j m : ℤ) :
    (∫ x in dyadicInterval j m, f x) ^ 2 ≤ ((2 : ℝ) ^ n)⁻¹ * (((2 : ℝ) ^ j)⁻¹ * ‖f‖ ^ 2) := by
  induction n generalizing j m with
  | zero => simpa using sq_integral_le_of_level j m f
  | succ n ih =>
    obtain ⟨q, hq⟩ : ∃ q : ℤ, ∫ x in dyadicInterval j m, f x =
        (∫ x in dyadicInterval (j - 1) q, f x) / 2 := by
      have h := integral_halves f hf (j - 1)
      simp only [sub_add_cancel] at h
      obtain ⟨q, rfl | rfl⟩ : ∃ q : ℤ, m = 2 * q ∨ m = 2 * q + 1 := ⟨m / 2, by omega⟩
      · exact ⟨q, (h q).1⟩
      · exact ⟨q, (h q).2⟩
    rw [hq]
    calc ((∫ x in dyadicInterval (j - 1) q, f x) / 2) ^ 2
        = (∫ x in dyadicInterval (j - 1) q, f x) ^ 2 / 4 := by ring
      _ ≤ ((2 : ℝ) ^ n)⁻¹ * (((2 : ℝ) ^ (j - 1))⁻¹ * ‖f‖ ^ 2) / 4 := by
        gcongr
        exact ih (j - 1) q
      _ = ((2 : ℝ) ^ (n + 1))⁻¹ * (((2 : ℝ) ^ j)⁻¹ * ‖f‖ ^ 2) := by
        rw [zpow_sub_one₀ two_ne_zero, pow_succ]
        field_simp
        ring

private lemma integral_eq_zero (f : Lp ℝ 2 (volume : Measure ℝ))
    (hf : ∀ jk, inner ℝ (haarVec jk) f = 0) (j m : ℤ) :
    ∫ x in dyadicInterval j m, f x = 0 := by
  have hlim : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ * (((2 : ℝ) ^ j)⁻¹ * ‖f‖ ^ 2)) atTop
      (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).mul_const (((2 : ℝ) ^ j)⁻¹ * ‖f‖ ^ 2)
  have hle : (∫ x in dyadicInterval j m, f x) ^ 2 ≤ 0 :=
    ge_of_tendsto' hlim fun n => sq_integral_le f hf n j m
  exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hle (sq_nonneg _))

private lemma haarVec_total : (Submodule.span ℝ (range haarVec))ᗮ = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro f hf
  have hortho (jk : ℤ × ℤ) : inner ℝ (haarVec jk) f = 0 :=
    hf _ (Submodule.subset_span (mem_range_self jk))
  have hlim := ae_tendsto_setAverage_dyadicInterval
    ((Lp.memLp f).locallyIntegrable (by norm_num) : LocallyIntegrable (⇑f) volume)
  rw [Submodule.mem_bot]
  apply Lp.ext
  filter_upwards [hlim, Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx hz
  have havg (n : ℕ) : ⨍ y in dyadicInterval n (dyadicIndex n x), f y = 0 := by
    rw [setAverage_eq, integral_eq_zero f hortho, smul_zero]
  simp only [havg] at hx
  exact (tendsto_nhds_unique hx tendsto_const_nhds).trans hz.symm

/-- **The Haar wavelet basis of `L²(ℝ)`** (S. Mallat, *Multiresolution approximations and
wavelet orthonormal bases of `L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989), Section 4, after (70):
the Haar basis is the wavelet orthonormal basis `√(2^j) ψ(2^j x - k)`, `(k, j) ∈ ℤ²`, of the
multiresolution approximation with scaling function `1_{[0,1]}`). The functions
`H_{j,k}(x) = 2^{j/2} H(2^j x - k)`, `j, k ∈ ℤ`, form an orthonormal basis of `L²(ℝ)`: there is
a Hilbert basis of `L²(ℝ)` indexed by `ℤ × ℤ` whose elements are a.e. equal to them. -/
theorem exists_hilbertBasis_haarSystem :
    ∃ b : HilbertBasis (ℤ × ℤ) ℝ (Lp ℝ 2 (volume : Measure ℝ)),
      ∀ jk : ℤ × ℤ, ⇑(b jk : Lp ℝ 2 (volume : Measure ℝ)) =ᵐ[volume] haarSystem jk.1 jk.2 := by
  refine ⟨HilbertBasis.mkOfOrthogonalEqBot haarVec_orthonormal haarVec_total, fun jk => ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact haarVec_ae jk

end

end MathlibExt.Analysis.Wavelet.HaarBasisWanted
