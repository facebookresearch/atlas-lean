/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Hilbert's inequality

Hilbert's inequality gives summability of the nonnegative double series and the
following bound for square-summable real sequences `a`, `b`,

```
∑' (m, n), |a m * b n| / ((m + 1) + (n + 1)) ≤ π * √(∑' m, (a m) ^ 2) * √(∑' n, (b n) ^ 2).
```

The proof follows the classical Schur-test argument. With the weights
`r n = 1 / √(n + 1)`, the row and column sums of the Hilbert kernel are
bounded by `π / √(m + 1)`: the series `∑_{n ≥ 1} 1 / ((m + n) * √n)` is
compared with the integral `∫₁^∞ dx / ((m + x) * √x)`, whose antiderivative
is `(2 / √m) * arctan √(x / m)`.

Source: D. Hilbert, *Grundzüge einer allgemeinen Theorie der linearen
Integralgleichungen*, 1906; see also Hardy–Littlewood–Pólya, *Inequalities*,
Theorem 323. This is a companion to the Fejér / Hardy-inequality material of
`v1/Atlas/IntroductionToFunctionalAnalysis` (the series form of Hardy's
inequality is in `MathlibExt/Analysis/Series/HardyInequality.lean`); it is
not one of the 72 v1 targets, and it is not in the pinned Mathlib (which has
no Hilbert-kernel or Hilbert-inequality statement). The constant `π` is
sharp; sharpness is not formalized here.
-/

@[expose] public section

namespace MathlibExt.Analysis.Series.HilbertInequality

open MeasureTheory Filter Topology

/-- The Hilbert kernel with `0`-based indices: `1 / ((m + 1) + (n + 1))`. -/
noncomputable def hilbertKernel (m n : ℕ) : ℝ := ((m : ℝ) + n + 2)⁻¹

/-- The row integrand `x ↦ 1 / ((M + x) * √x)` used to bound the row sums
of the Hilbert kernel by an integral. -/
noncomputable def hilbertKernelRow (M : ℝ) (x : ℝ) : ℝ := ((M + x) * Real.sqrt x)⁻¹

/-- The Hilbert kernel is nonnegative. -/
theorem hilbertKernel_nonneg (m n : ℕ) : 0 ≤ hilbertKernel m n := by
  rw [hilbertKernel]
  positivity

/-- The row integrand is nonnegative on `(0, ∞)` when `M > 0`. -/
theorem hilbertKernelRow_nonneg {M : ℝ} (hM : 0 < M) {x : ℝ} (hx : 0 < x) :
    0 ≤ hilbertKernelRow M x := by
  rw [hilbertKernelRow]
  positivity

/-- The row integrand is continuous on `(0, ∞)` when `M > 0`. -/
theorem hilbertKernelRow_continuousOn {M : ℝ} (hM : 0 < M) :
    ContinuousOn (hilbertKernelRow M) (Set.Ioi 0) := by
  apply ContinuousOn.inv₀
  · exact ((continuous_const.add continuous_id').mul
      (Real.continuous_sqrt.comp continuous_id')).continuousOn
  · intro x hx
    have hx' : 0 < x := hx
    have h1 : 0 < M + x := by linarith
    have h2 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx'
    exact mul_ne_zero h1.ne' h2.ne'

/-- The row integrand is antitone on `[1, ∞)` when `M > 0`. -/
theorem hilbertKernelRow_antitoneOn {M : ℝ} (hM : 0 < M) :
    AntitoneOn (hilbertKernelRow M) (Set.Ici 1) := by
  intro x hx y hy hxy
  have hx1 : (1:ℝ) ≤ x := hx
  have hy1 : (1:ℝ) ≤ y := hy
  rw [hilbertKernelRow, hilbertKernelRow, ← one_div, ← one_div]
  apply one_div_le_one_div_of_le
  · have hx' : (0:ℝ) < x := by linarith
    have h1 : 0 < M + x := by linarith
    have h2 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx'
    exact mul_pos h1 h2
  · have h1 : M + x ≤ M + y := by linarith
    have h2 : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
    have h3 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
    exact mul_le_mul h1 h2 h3 (by linarith)

/-- The derivative of the antiderivative `(2 / √M) * arctan √(x / M)`. -/
theorem hasDerivAt_hilbertAntideriv {M : ℝ} (hM : 0 < M) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun x => (2 / Real.sqrt M) * Real.arctan (Real.sqrt (x / M)))
      (hilbertKernelRow M x) x := by
  have hM' : (M : ℝ) ≠ 0 := hM.ne'
  have hx' : (x : ℝ) ≠ 0 := hx.ne'
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hdiv : HasDerivAt (fun x : ℝ => x / M) (1 / M) x :=
    (hasDerivAt_id x).div_const M
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (x / M))
      (1 / (2 * Real.sqrt (x / M)) * (1 / M)) x :=
    (Real.hasDerivAt_sqrt (by positivity : x / M ≠ 0)).comp x hdiv
  have harctan : HasDerivAt (fun x : ℝ => Real.arctan (Real.sqrt (x / M)))
      (1 / (1 + (Real.sqrt (x / M)) ^ 2) * (1 / (2 * Real.sqrt (x / M)) * (1 / M))) x :=
    (Real.hasDerivAt_arctan _).comp x hsqrt
  have hmul := harctan.const_mul (2 / Real.sqrt M)
  refine hmul.congr_deriv ?_
  have h1 : Real.sqrt (x / M) = Real.sqrt x / Real.sqrt M := Real.sqrt_div hx.le M
  have h2 : (Real.sqrt (x / M)) ^ 2 = x / M := Real.sq_sqrt (by positivity)
  rw [hilbertKernelRow, h2, h1]
  field_simp

/-- The finite integral of the row integrand, via its antiderivative. -/
theorem intervalIntegral_hilbertKernelRow {M : ℝ} (hM : 0 < M) {B : ℝ} (hB : 1 ≤ B) :
    ∫ x in (1:ℝ)..B, hilbertKernelRow M x =
      (2 / Real.sqrt M) *
        (Real.arctan (Real.sqrt (B / M)) - Real.arctan (Real.sqrt (1 / M))) := by
  have hcont : ContinuousOn (fun x => (2 / Real.sqrt M) * Real.arctan (Real.sqrt (x / M)))
      (Set.Icc 1 B) := by
    apply ContinuousOn.mul continuousOn_const
    exact (Real.continuous_arctan.comp
      (Real.continuous_sqrt.comp (continuous_id'.div_const M))).continuousOn
  have hderiv : ∀ x ∈ Set.Ioo (1:ℝ) B,
      HasDerivAt (fun x => (2 / Real.sqrt M) * Real.arctan (Real.sqrt (x / M)))
        (hilbertKernelRow M x) x :=
    fun x hx => hasDerivAt_hilbertAntideriv hM (by linarith [hx.1])
  have hint : IntervalIntegrable (hilbertKernelRow M) MeasureTheory.volume 1 B := by
    apply ContinuousOn.intervalIntegrable
    apply (hilbertKernelRow_continuousOn hM).mono
    intro x hx
    rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact Set.mem_Ioi.mpr (by linarith)
    · exact Set.mem_Ioi.mpr (by linarith)
  rw [mul_sub]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hB hcont hderiv hint

/-- The row integrand is integrable on `(1, ∞)`, with a uniform bound on
the interval integrals. -/
theorem integrableOn_Ioi_hilbertKernelRow {M : ℝ} (hM : 0 < M) :
    IntegrableOn (hilbertKernelRow M) (Set.Ioi 1) := by
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded (Real.pi / Real.sqrt M) 1
    (b := fun i : ℕ => (i : ℝ)) (l := atTop)
  · intro i
    by_cases hi : (1:ℝ) ≤ (i:ℝ)
    · apply IntegrableOn.mono_set _ Set.Ioc_subset_Icc_self
      apply ContinuousOn.integrableOn_Icc
      apply (hilbertKernelRow_continuousOn hM).mono
      intro x hx
      exact Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one hx.1)
    · rw [Set.Ioc_eq_empty (by linarith : ¬ (1:ℝ) < (i:ℝ))]
      exact integrableOn_empty
  · exact tendsto_natCast_atTop_atTop
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with i hi
    have hi' : (1:ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    have hcongr : (∫ x in (1:ℝ)..(i:ℝ), ‖hilbertKernelRow M x‖) =
        ∫ x in (1:ℝ)..(i:ℝ), hilbertKernelRow M x := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hi'] at hx
      have hx' : (0:ℝ) < x := by linarith [hx.1]
      show ‖hilbertKernelRow M x‖ = hilbertKernelRow M x
      rw [Real.norm_of_nonneg (hilbertKernelRow_nonneg hM hx')]
    rw [hcongr, intervalIntegral_hilbertKernelRow hM hi']
    have h1 : Real.arctan (Real.sqrt ((i:ℝ) / M)) < Real.pi / 2 :=
      Real.arctan_lt_pi_div_two _
    have h2 : 0 ≤ Real.arctan (Real.sqrt (1 / M)) :=
      Real.arctan_nonneg.mpr (Real.sqrt_nonneg _)
    have h3 : 0 ≤ (2:ℝ) / Real.sqrt M := by positivity
    calc (2 / Real.sqrt M) *
            (Real.arctan (Real.sqrt ((i:ℝ) / M)) - Real.arctan (Real.sqrt (1 / M)))
        ≤ (2 / Real.sqrt M) * (Real.pi / 2) := by
          apply mul_le_mul_of_nonneg_left _ h3
          linarith
      _ = Real.pi / Real.sqrt M := by
        rw [div_mul_div_comm, mul_comm (2:ℝ) Real.pi,
          mul_div_mul_right _ _ (by norm_num : (2:ℝ) ≠ 0)]

/-- The improper integral of the row integrand over `(1, ∞)`. -/
theorem integral_Ioi_hilbertKernelRow {M : ℝ} (hM : 0 < M) :
    ∫ x in Set.Ioi (1:ℝ), hilbertKernelRow M x =
      (2 / Real.sqrt M) * (Real.pi / 2 - Real.arctan (Real.sqrt (1 / M))) := by
  have hfi := integrableOn_Ioi_hilbertKernelRow hM
  have hlim := intervalIntegral_tendsto_integral_Ioi (1:ℝ) hfi
    (b := fun i : ℕ => (i : ℝ)) (l := atTop) tendsto_natCast_atTop_atTop
  have hval : Tendsto (fun i : ℕ => ∫ x in (1:ℝ)..(i:ℝ), hilbertKernelRow M x) atTop
      (𝓝 ((2 / Real.sqrt M) * (Real.pi / 2 - Real.arctan (Real.sqrt (1 / M))))) := by
    have h1 : Tendsto (fun i : ℕ => Real.arctan (Real.sqrt ((i:ℝ) / M))) atTop
        (𝓝 (Real.pi / 2)) := by
      have h2 : Tendsto (fun i : ℕ => ((i:ℝ) / M)) atTop atTop :=
        Tendsto.atTop_div_const hM tendsto_natCast_atTop_atTop
      have h3 : Tendsto (fun i : ℕ => Real.sqrt ((i:ℝ) / M)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp h2
      have h4 := Real.tendsto_arctan_atTop.comp h3
      exact h4.mono_right nhdsWithin_le_nhds
    have h5 : Tendsto (fun i : ℕ => (2 / Real.sqrt M) *
        (Real.arctan (Real.sqrt ((i:ℝ) / M)) - Real.arctan (Real.sqrt (1 / M)))) atTop
        (𝓝 ((2 / Real.sqrt M) * (Real.pi / 2 - Real.arctan (Real.sqrt (1 / M))))) :=
      (h1.sub tendsto_const_nhds).const_mul _
    refine h5.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with i hi
    have hi' : (1:ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    exact (intervalIntegral_hilbertKernelRow hM hi').symm
  exact tendsto_nhds_unique hlim hval

/-- A lower bound for `arctan`: `t / (1 + t ^ 2) ≤ arctan t` for `t ≥ 0`. -/
theorem div_one_add_sq_le_arctan {t : ℝ} (ht : 0 ≤ t) :
    t / (1 + t ^ 2) ≤ Real.arctan t := by
  have h0 : (0:ℝ) ≤ t := ht
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · rw [← ht0]
    simp
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) t,
      HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x :=
    fun x _ => Real.hasDerivAt_arctan x
  have hcont : ContinuousOn Real.arctan (Set.Icc 0 t) :=
    Real.continuous_arctan.continuousOn
  have hint : IntervalIntegrable (fun x : ℝ => 1 / (1 + x ^ 2)) MeasureTheory.volume 0 t :=
    (continuous_const.div (continuous_const.add (continuous_pow 2))
      (fun x => ne_of_gt (by positivity : (0:ℝ) < 1 + x ^ 2))).intervalIntegrable 0 t
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0 hcont hderiv hint
  rw [Real.arctan_zero, sub_zero] at hftc
  rw [← hftc]
  have hmono : (∫ x in (0:ℝ)..t, (1 / (1 + t ^ 2) : ℝ)) ≤
      ∫ x in (0:ℝ)..t, (1 / (1 + x ^ 2) : ℝ) := by
    apply intervalIntegral.integral_mono_on h0 intervalIntegrable_const hint
    intro x hx
    have hx1 : x ≤ t := hx.2
    have hx2 : x ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hx.1 hx1 2
    apply one_div_le_one_div_of_le
    · positivity
    · linarith
  have hconst : (∫ _x in (0:ℝ)..t, (1 / (1 + t ^ 2) : ℝ)) = t / (1 + t ^ 2) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    ring
  rwa [hconst] at hmono

/-- The `n`-th term of the row series, `1 / ((M + (n + 1)) * √((n + 1)))`,
as a function of `n : ℕ`. -/
noncomputable def hilbertKernelRowSeq (M : ℝ) (n : ℕ) : ℝ :=
  hilbertKernelRow M ((n : ℝ) + 1)

/-- Summability of the row series. -/
theorem summable_hilbertKernelRowSeq {M : ℝ} (hM : 0 < M) :
    Summable (hilbertKernelRowSeq M) := by
  have hanti : AntitoneOn (hilbertKernelRow M) (Set.Ici 1) :=
    hilbertKernelRow_antitoneOn hM
  have hanti1 : AntitoneOn (hilbertKernelRow M) (Set.Ici ((1 : ℕ) : ℝ)) := by
    exact_mod_cast hanti
  have hfi1 : IntegrableOn (hilbertKernelRow M) (Set.Ioi ((1 : ℕ) : ℝ)) := by
    exact_mod_cast integrableOn_Ioi_hilbertKernelRow hM
  have hsum : Summable (fun n : ℕ => hilbertKernelRow M (n : ℝ)) :=
    hanti1.summable_of_integrableOn_Ioi (N := 1) hfi1
      (fun x hx => hilbertKernelRow_nonneg hM (by
        have h1x : (1:ℝ) < x := by exact_mod_cast Set.mem_Ioi.mp hx
        linarith))
  have h := (summable_nat_add_iff (1 : ℕ)).mpr hsum
  refine h.congr ?_
  intro n
  show hilbertKernelRow M (↑(n + 1)) = hilbertKernelRow M (↑n + 1)
  congr 1
  push_cast
  ring

/-- Summability of the row series in unfurled form. -/
theorem summable_hilbertKernelRow {M : ℝ} (hM : 0 < M) :
    Summable (fun n : ℕ => ((M + ((n:ℝ) + 1)) * Real.sqrt ((n:ℝ) + 1))⁻¹) := by
  refine (summable_hilbertKernelRowSeq hM).congr ?_
  intro n
  show hilbertKernelRow M (↑n + 1) =
    ((M + ((n:ℝ) + 1)) * Real.sqrt ((n:ℝ) + 1))⁻¹
  rw [hilbertKernelRow]

/-- The row sum of the Hilbert kernel is at most `π / √(m + 1)`. -/
theorem hilbertKernel_row_sum_le (m : ℕ) :
    ∑' (n : ℕ), hilbertKernel m n * (Real.sqrt ((n:ℝ) + 1))⁻¹ ≤
      Real.pi / Real.sqrt ((m:ℝ) + 1) := by
  set M : ℝ := (m : ℝ) + 1 with hMdef
  have hM : 0 < M := by positivity
  have hterm : ∀ n : ℕ, hilbertKernel m n * (Real.sqrt ((n:ℝ) + 1))⁻¹ =
      hilbertKernelRowSeq M n := by
    intro n
    have h1 : ((m:ℝ) + (n:ℝ) + 2) = (M + ((n:ℝ) + 1)) := by
      rw [hMdef]
      ring
    rw [hilbertKernel, hilbertKernelRowSeq, hilbertKernelRow, mul_inv, h1]
  rw [tsum_congr hterm]
  have hanti : AntitoneOn (hilbertKernelRow M) (Set.Ici 1) :=
    hilbertKernelRow_antitoneOn hM
  have hfi : IntegrableOn (hilbertKernelRow M) (Set.Ioi 1) :=
    integrableOn_Ioi_hilbertKernelRow hM
  have hshift : Summable (hilbertKernelRowSeq M) := summable_hilbertKernelRowSeq hM
  have hsplit : ∑' (n : ℕ), hilbertKernelRowSeq M n =
      hilbertKernelRow M 1 + ∑' (n : ℕ), hilbertKernelRowSeq M (n + 1) := by
    have h := hshift.tsum_eq_zero_add
    have h0 : hilbertKernelRowSeq M 0 = hilbertKernelRow M 1 := by
      simp only [hilbertKernelRowSeq, Nat.cast_zero, zero_add]
    rw [h0] at h
    exact h
  have htail : ∑' (n : ℕ), hilbertKernelRowSeq M (n + 1) ≤
      ∫ x in Set.Ioi (1:ℝ), hilbertKernelRow M x := by
    have hfi1 : IntegrableOn (hilbertKernelRow M) (Set.Ioi ((1 : ℕ) : ℝ)) := by
      exact_mod_cast hfi
    have hanti1 : AntitoneOn (hilbertKernelRow M) (Set.Ici ((1 : ℕ) : ℝ)) := by
      exact_mod_cast hanti
    have h := hanti1.tsum_comp_add_le_integral (N := 1) hfi1
      (fun x hx => hilbertKernelRow_nonneg hM (by
        have h1x : (1:ℝ) < x := by exact_mod_cast Set.mem_Ioi.mp hx
        linarith))
    have h2 : ∑' (n : ℕ), hilbertKernelRow M (↑(n + 1 + 1)) ≤
        ∫ x in Set.Ioi (1:ℝ), hilbertKernelRow M x := by
      exact_mod_cast h
    refine le_trans (le_of_eq (tsum_congr ?_)) h2
    intro n
    show hilbertKernelRow M (↑(n + 1) + 1) = hilbertKernelRow M ↑(n + 1 + 1)
    congr 1
    push_cast
    ring
  rw [hsplit]
  refine le_trans (by gcongr : hilbertKernelRow M 1 +
      ∑' (n : ℕ), hilbertKernelRowSeq M (n + 1) ≤ hilbertKernelRow M 1 +
      ∫ x in Set.Ioi (1:ℝ), hilbertKernelRow M x) ?_
  rw [integral_Ioi_hilbertKernelRow hM]
  have hrow1 : hilbertKernelRow M 1 = 1 / (M + 1) := by
    simp [hilbertKernelRow, Real.sqrt_one, one_div]
  rw [hrow1]
  have hsqrt1 : Real.sqrt (1 / M) = 1 / Real.sqrt M := by
    rw [Real.sqrt_div zero_le_one M, Real.sqrt_one]
  rw [hsqrt1]
  have hsqrtM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hM1 : (1:ℝ) ≤ M := by linarith
  have hbound : 1 / (M + 1) ≤ (2 / Real.sqrt M) * Real.arctan (1 / Real.sqrt M) := by
    have ht : (0:ℝ) ≤ 1 / Real.sqrt M := by positivity
    have ht1 : 1 / Real.sqrt M ≤ 1 := by
      rw [div_le_one hsqrtM]
      have h := Real.sqrt_le_sqrt hM1
      rwa [Real.sqrt_one] at h
    have h1 : (1 / Real.sqrt M) / 2 ≤ Real.arctan (1 / Real.sqrt M) := by
      have h2 := div_one_add_sq_le_arctan ht
      have h3 : (1 / Real.sqrt M) / 2 ≤
          (1 / Real.sqrt M) / (1 + (1 / Real.sqrt M) ^ 2) := by
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2)
          (by positivity : (0:ℝ) < 1 + (1 / Real.sqrt M) ^ 2)]
        have h4 : (1 / Real.sqrt M) ^ 2 ≤ 1 := by
          rw [div_pow, one_pow, Real.sq_sqrt hM.le, div_le_one hM]
          exact hM1
        exact mul_le_mul_of_nonneg_left (by linarith) ht
      exact le_trans h3 h2
    have h2 : (2 / Real.sqrt M) * ((1 / Real.sqrt M) / 2) = 1 / M := by
      field_simp
      nlinarith [Real.mul_self_sqrt hM.le]
    calc 1 / (M + 1) ≤ 1 / M := one_div_le_one_div_of_le (by linarith) (by linarith)
      _ = (2 / Real.sqrt M) * ((1 / Real.sqrt M) / 2) := h2.symm
      _ ≤ (2 / Real.sqrt M) * Real.arctan (1 / Real.sqrt M) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
  have hpi : Real.pi / Real.sqrt M - (2 / Real.sqrt M) * Real.arctan (1 / Real.sqrt M) +
      1 / (M + 1) ≤ Real.pi / Real.sqrt M := by linarith [hbound]
  calc 1 / (M + 1) + (2 / Real.sqrt M) * (Real.pi / 2 - Real.arctan (1 / Real.sqrt M))
      = Real.pi / Real.sqrt M - (2 / Real.sqrt M) * Real.arctan (1 / Real.sqrt M) +
        1 / (M + 1) := by
        rw [mul_sub, div_mul_div_comm, mul_comm (2:ℝ) Real.pi,
          mul_div_mul_right _ _ (by norm_num : (2:ℝ) ≠ 0)]
        ring
    _ ≤ Real.pi / Real.sqrt M := hpi


/-- The Hilbert kernel is symmetric. -/
theorem hilbertKernel_symm (m n : ℕ) : hilbertKernel m n = hilbertKernel n m := by
  rw [hilbertKernel, hilbertKernel]
  congr 1
  ring

/-- The Schur test for finite bilinear forms: a weighted row/column bound
implies a bound on the bilinear form with constant `√(α * β)`. -/
theorem schurTest_finite {N : ℕ} {A : ℕ → ℕ → ℝ} {a b r c : ℕ → ℝ} {α β : ℝ}
    (hA : ∀ m n, 0 ≤ A m n) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hr : ∀ n, 0 < r n) (hc : ∀ n, 0 < c n) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hrow : ∀ m, ∑ n ∈ Finset.range N, A m n * r n ≤ α * c m)
    (hcol : ∀ n, ∑ m ∈ Finset.range N, A m n * c m ≤ β * r n) :
    ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, A m n * a m * b n ≤
      Real.sqrt (α * β) * Real.sqrt (∑ m ∈ Finset.range N, (a m) ^ 2) *
        Real.sqrt (∑ n ∈ Finset.range N, (b n) ^ 2) := by
  classical
  set X : ℕ → ℕ → ℝ := fun m n => Real.sqrt (A m n * r n / c m) * a m with hX
  set Y : ℕ → ℕ → ℝ := fun m n => Real.sqrt (A m n * c m / r n) * b n with hY
  have hXY : ∀ m n, X m n * Y m n = A m n * a m * b n := by
    intro m n
    have h1 : Real.sqrt (A m n * r n / c m) * Real.sqrt (A m n * c m / r n) =
        A m n := by
      rw [← Real.sqrt_mul (div_nonneg (mul_nonneg (hA m n) (hr n).le) (hc m).le)]
      have hrn : r n ≠ 0 := (hr n).ne'
      have hcn : c m ≠ 0 := (hc m).ne'
      have h2 : (A m n * r n / c m) * (A m n * c m / r n) = (A m n) ^ 2 := by
        rw [div_mul_div_comm, div_eq_iff (mul_ne_zero hcn hrn)]
        ring
      rw [h2, Real.sqrt_sq (hA m n)]
    calc X m n * Y m n
        = (Real.sqrt (A m n * r n / c m) * Real.sqrt (A m n * c m / r n)) *
          (a m * b n) := by rw [hX, hY]; ring
      _ = A m n * a m * b n := by rw [h1]; ring
  have hX2 : ∀ m n, (X m n) ^ 2 = (A m n * r n / c m) * (a m) ^ 2 := by
    intro m n
    rw [hX, mul_pow,
      Real.sq_sqrt (div_nonneg (mul_nonneg (hA m n) (hr n).le) (hc m).le)]
  have hY2 : ∀ m n, (Y m n) ^ 2 = (A m n * c m / r n) * (b n) ^ 2 := by
    intro m n
    rw [hY, mul_pow,
      Real.sq_sqrt (div_nonneg (mul_nonneg (hA m n) (hc m).le) (hr n).le)]
  have hsumX : ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, (X m n) ^ 2 ≤
      α * ∑ m ∈ Finset.range N, (a m) ^ 2 := by
    calc ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, (X m n) ^ 2
        = ∑ m ∈ Finset.range N, ((a m) ^ 2 / c m) * (∑ n ∈ Finset.range N, A m n * r n) := by
          apply Finset.sum_congr rfl
          intro m _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          rw [hX2,
            div_mul_eq_mul_div (A m n * r n) (c m) ((a m) ^ 2),
            div_mul_eq_mul_div ((a m) ^ 2) (c m) (A m n * r n)]
          congr 1
          ring
      _ ≤ ∑ m ∈ Finset.range N, ((a m) ^ 2 / c m) * (α * c m) := by
          apply Finset.sum_le_sum
          intro m _
          apply mul_le_mul_of_nonneg_left (hrow m)
          exact div_nonneg (sq_nonneg _) (hc m).le
      _ = α * ∑ m ∈ Finset.range N, (a m) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          rw [div_mul_eq_mul_div, div_eq_iff (hc m).ne']
          ring
  have hsumY : ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, (Y m n) ^ 2 ≤
      β * ∑ n ∈ Finset.range N, (b n) ^ 2 := by
    calc ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, (Y m n) ^ 2
        = ∑ n ∈ Finset.range N, ((b n) ^ 2 / r n) * (∑ m ∈ Finset.range N, A m n * c m) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro n _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _
          rw [hY2,
            div_mul_eq_mul_div (A m n * c m) (r n) ((b n) ^ 2),
            div_mul_eq_mul_div ((b n) ^ 2) (r n) (A m n * c m)]
          congr 1
          ring
      _ ≤ ∑ n ∈ Finset.range N, ((b n) ^ 2 / r n) * (β * r n) := by
          apply Finset.sum_le_sum
          intro n _
          apply mul_le_mul_of_nonneg_left (hcol n)
          exact div_nonneg (sq_nonneg _) (hr n).le
      _ = β * ∑ n ∈ Finset.range N, (b n) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _
          rw [div_mul_eq_mul_div, div_eq_iff (hr n).ne']
          ring
  set S : ℝ := ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N, A m n * a m * b n with hS
  have hS_eq : S = ∑ p ∈ Finset.range N ×ˢ Finset.range N, X p.1 p.2 * Y p.1 p.2 := by
    rw [hS, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    exact (hXY m n).symm
  have hS_nonneg : 0 ≤ S := by
    rw [hS]
    apply Finset.sum_nonneg
    intro m _
    apply Finset.sum_nonneg
    intro n _
    exact mul_nonneg (mul_nonneg (hA m n) (ha m)) (hb n)
  have hCS' : S ^ 2 ≤ (α * ∑ m ∈ Finset.range N, (a m) ^ 2) *
      (β * ∑ n ∈ Finset.range N, (b n) ^ 2) := by
    rw [hS_eq]
    have hCS2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N ×ˢ Finset.range N)
      (fun p => X p.1 p.2) (fun p => Y p.1 p.2)
    refine hCS2.trans (mul_le_mul ?_ ?_
      (Finset.sum_nonneg (fun p _ => sq_nonneg _))
      (mul_nonneg hα (Finset.sum_nonneg (fun m _ => sq_nonneg _))))
    · rw [Finset.sum_product]
      exact hsumX
    · rw [Finset.sum_product]
      exact hsumY
  have hsqrt : S ≤ Real.sqrt ((α * ∑ m ∈ Finset.range N, (a m) ^ 2) *
      (β * ∑ n ∈ Finset.range N, (b n) ^ 2)) := by
    rw [← Real.sqrt_sq hS_nonneg]
    exact Real.sqrt_le_sqrt hCS'
  rw [Real.sqrt_mul (mul_nonneg hα (Finset.sum_nonneg (fun m _ => sq_nonneg _)))] at hsqrt
  calc S ≤ Real.sqrt (α * ∑ m ∈ Finset.range N, (a m) ^ 2) *
        Real.sqrt (β * ∑ n ∈ Finset.range N, (b n) ^ 2) := hsqrt
    _ = Real.sqrt (α * β) * Real.sqrt (∑ m ∈ Finset.range N, (a m) ^ 2) *
        Real.sqrt (∑ n ∈ Finset.range N, (b n) ^ 2) := by
      rw [Real.sqrt_mul hα, Real.sqrt_mul hβ]
      calc (Real.sqrt α * Real.sqrt (∑ m ∈ Finset.range N, (a m) ^ 2)) *
              (Real.sqrt β * Real.sqrt (∑ n ∈ Finset.range N, (b n) ^ 2))
          = (Real.sqrt α * Real.sqrt β) * Real.sqrt (∑ m ∈ Finset.range N, (a m) ^ 2) *
              Real.sqrt (∑ n ∈ Finset.range N, (b n) ^ 2) := by ring
        _ = Real.sqrt (α * β) * Real.sqrt (∑ m ∈ Finset.range N, (a m) ^ 2) *
              Real.sqrt (∑ n ∈ Finset.range N, (b n) ^ 2) := by
            rw [← Real.sqrt_mul hα β]

/-- The finite form of Hilbert's inequality, from the Schur test with the
weights `r n = 1 / √(n + 1)` and the row bound `hilbertKernel_row_sum_le`. -/
theorem hilbert_inequality_finite {N : ℕ} {a b : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n) :
    ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      a m * b n / ((m:ℝ) + n + 2) ≤
      Real.pi * Real.sqrt (∑ m ∈ Finset.range N, (a m) ^ 2) *
        Real.sqrt (∑ n ∈ Finset.range N, (b n) ^ 2) := by
  have h := schurTest_finite (N := N) (A := hilbertKernel) (a := a) (b := b)
    (r := fun n => (Real.sqrt ((n:ℝ) + 1))⁻¹) (c := fun n => (Real.sqrt ((n:ℝ) + 1))⁻¹)
    (α := Real.pi) (β := Real.pi)
    (fun m n => hilbertKernel_nonneg m n) ha hb
    (fun n => inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)))
    (fun n => inv_pos.mpr (Real.sqrt_pos.mpr (by positivity)))
    Real.pi_nonneg Real.pi_nonneg
    (by
      intro m
      have hrow := hilbertKernel_row_sum_le m
      have hsum : Summable (fun n : ℕ => hilbertKernel m n * (Real.sqrt ((n:ℝ) + 1))⁻¹) := by
        have h := summable_hilbertKernelRow (M := (m:ℝ) + 1) (by positivity)
        refine h.congr ?_
        intro n
        rw [hilbertKernel, mul_inv]
        congr 1
        congr 1
        ring
      calc ∑ n ∈ Finset.range N, hilbertKernel m n * (Real.sqrt ((n:ℝ) + 1))⁻¹
          ≤ ∑' (n : ℕ), hilbertKernel m n * (Real.sqrt ((n:ℝ) + 1))⁻¹ :=
            hsum.sum_le_tsum _ (fun n _ => mul_nonneg (hilbertKernel_nonneg m n)
              (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        _ ≤ Real.pi / Real.sqrt ((m:ℝ) + 1) := hrow
        _ = Real.pi * (Real.sqrt ((m:ℝ) + 1))⁻¹ := by rw [div_eq_mul_inv])
    (by
      intro n
      have hrow := hilbertKernel_row_sum_le n
      have hsum : Summable (fun m : ℕ => hilbertKernel m n * (Real.sqrt ((m:ℝ) + 1))⁻¹) := by
        have h := summable_hilbertKernelRow (M := (n:ℝ) + 1) (by positivity)
        refine h.congr ?_
        intro m
        rw [hilbertKernel]
        have hsym : ((m:ℝ) + n + 2) = ((n:ℝ) + m + 2) := by ring
        rw [hsym, mul_inv]
        congr 1
        congr 1
        ring
      calc ∑ m ∈ Finset.range N, hilbertKernel m n * (Real.sqrt ((m:ℝ) + 1))⁻¹
          ≤ ∑' (m : ℕ), hilbertKernel m n * (Real.sqrt ((m:ℝ) + 1))⁻¹ :=
            hsum.sum_le_tsum _ (fun m _ => mul_nonneg (hilbertKernel_nonneg m n)
              (inv_nonneg.mpr (Real.sqrt_nonneg _)))
        _ = ∑' (m : ℕ), hilbertKernel n m * (Real.sqrt ((m:ℝ) + 1))⁻¹ :=
            tsum_congr (fun m => by rw [hilbertKernel_symm m n])
        _ ≤ Real.pi / Real.sqrt ((n:ℝ) + 1) := hrow
        _ = Real.pi * (Real.sqrt ((n:ℝ) + 1))⁻¹ := by rw [div_eq_mul_inv])
  rw [Real.sqrt_mul_self Real.pi_nonneg] at h
  refine le_trans (le_of_eq ?_) h
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  rw [hilbertKernel, div_eq_mul_inv]
  ring

/-- The common finite-sum proof gives absolute convergence and the Hilbert bound. -/
private theorem summable_and_hilbert_inequality {a b : ℕ → ℝ}
    (ha : Summable (fun n => (a n) ^ 2)) (hb : Summable (fun n => (b n) ^ 2)) :
    Summable (fun p : ℕ × ℕ => |a p.1 * b p.2| * hilbertKernel p.1 p.2) ∧
    ∑' (p : ℕ × ℕ), |a p.1 * b p.2| * hilbertKernel p.1 p.2 ≤
      Real.pi * Real.sqrt (∑' (n : ℕ), (a n) ^ 2) *
        Real.sqrt (∑' (n : ℕ), (b n) ^ 2) := by
  set C : ℝ := Real.pi * Real.sqrt (∑' (n : ℕ), (a n) ^ 2) *
    Real.sqrt (∑' (n : ℕ), (b n) ^ 2) with hC
  set F : ℕ × ℕ → ℝ := fun p => |a p.1 * b p.2| * hilbertKernel p.1 p.2 with hF
  have hF_nonneg : ∀ p, 0 ≤ F p := fun p =>
    mul_nonneg (abs_nonneg _) (hilbertKernel_nonneg _ _)
  have hbound : ∀ s : Finset (ℕ × ℕ), ∑ p ∈ s, F p ≤ C := by
    intro s
    classical
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ p ∈ s, p.1 < N ∧ p.2 < N := by
      refine ⟨(s.sup fun p => p.1 + p.2) + 1, fun p hp => ?_⟩
      have hle : p.1 + p.2 ≤ s.sup (fun p : ℕ × ℕ => p.1 + p.2) :=
        Finset.le_sup (f := fun p : ℕ × ℕ => p.1 + p.2) hp
      constructor <;> omega
    have hsub : s ⊆ Finset.range N ×ˢ Finset.range N := by
      intro p hp
      rw [Finset.mem_product]
      exact ⟨Finset.mem_range.mpr (hN p hp).1, Finset.mem_range.mpr (hN p hp).2⟩
    calc ∑ p ∈ s, F p ≤ ∑ p ∈ Finset.range N ×ˢ Finset.range N, F p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hF_nonneg p)
      _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          |a m| * |b n| / ((m:ℝ) + n + 2) := by
          rw [Finset.sum_product]
          apply Finset.sum_congr rfl
          intro m _
          apply Finset.sum_congr rfl
          intro n _
          show |a m * b n| * hilbertKernel m n = |a m| * |b n| / ((m:ℝ) + n + 2)
          rw [abs_mul, hilbertKernel, div_eq_mul_inv]
      _ ≤ Real.pi * Real.sqrt (∑ m ∈ Finset.range N, (|a m|) ^ 2) *
          Real.sqrt (∑ n ∈ Finset.range N, (|b n|) ^ 2) :=
        hilbert_inequality_finite (fun n => abs_nonneg _) (fun n => abs_nonneg _)
      _ ≤ C := by
        rw [hC]
        have h1 : ∑ m ∈ Finset.range N, (|a m|) ^ 2 ≤ ∑' (n : ℕ), (a n) ^ 2 := by
          calc ∑ m ∈ Finset.range N, (|a m|) ^ 2
              = ∑ m ∈ Finset.range N, (a m) ^ 2 := by
                apply Finset.sum_congr rfl
                intro m _
                rw [sq_abs]
            _ ≤ ∑' (n : ℕ), (a n) ^ 2 :=
                ha.sum_le_tsum _ (fun n _ => sq_nonneg _)
        have h2 : ∑ n ∈ Finset.range N, (|b n|) ^ 2 ≤ ∑' (n : ℕ), (b n) ^ 2 := by
          calc ∑ n ∈ Finset.range N, (|b n|) ^ 2
              = ∑ n ∈ Finset.range N, (b n) ^ 2 := by
                apply Finset.sum_congr rfl
                intro n _
                rw [sq_abs]
            _ ≤ ∑' (n : ℕ), (b n) ^ 2 :=
                hb.sum_le_tsum _ (fun n _ => sq_nonneg _)
        gcongr
  exact ⟨summable_of_sum_le hF_nonneg hbound,
    Real.tsum_le_of_sum_le hF_nonneg hbound⟩


/-- The nonnegative Hilbert double series is summable for square-summable inputs. -/
theorem summable_hilbert_terms {a b : ℕ → ℝ}
    (ha : Summable (fun n => (a n) ^ 2)) (hb : Summable (fun n => (b n) ^ 2)) :
    Summable (fun p : ℕ × ℕ => |a p.1 * b p.2| * hilbertKernel p.1 p.2) :=
  (summable_and_hilbert_inequality ha hb).1

/-- Hilbert's inequality for square-summable real sequences. -/
theorem hilbert_inequality {a b : ℕ → ℝ}
    (ha : Summable (fun n => (a n) ^ 2)) (hb : Summable (fun n => (b n) ^ 2)) :
    ∑' (p : ℕ × ℕ), |a p.1 * b p.2| * hilbertKernel p.1 p.2 ≤
      Real.pi * Real.sqrt (∑' (n : ℕ), (a n) ^ 2) *
        Real.sqrt (∑' (n : ℕ), (b n) ^ 2) :=
  (summable_and_hilbert_inequality ha hb).2

end MathlibExt.Analysis.Series.HilbertInequality
