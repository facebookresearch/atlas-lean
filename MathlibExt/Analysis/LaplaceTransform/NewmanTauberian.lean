/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import MathlibExt.Analysis.LaplaceTransform.ExponentialBound
import MathlibExt.Analysis.PerronKernel
public import MathlibExt.Analysis.LaplaceTransform.Basic

/-!
# Newman's Tauberian theorem

Newman's analytic (Tauberian) theorem for a bounded measurable function whose Laplace
transform extends analytically to the closed right half-plane. Following D. J. Newman,
"Simple analytic proof of the prime number theorem", Amer. Math. Monthly 87 (1980)
693–696, in the form of D. Zagier, "Newman's short proof of the prime number theorem",
Amer. Math. Monthly 104 (1997) 705–708.
-/

@[expose] public section

open Filter MeasureTheory Set Topology

/-- Newman kernel `k_R(z) = (1 + z^2 / R^2) / z`. At `z = 0` this is junk (0). -/
private noncomputable def newman_kernel (R : ℝ) (z : ℂ) : ℂ :=
  (1 + z ^ 2 / (R : ℂ) ^ 2) / z

/-- Partial Laplace transform `g_T(z) = ∫ t in 0..T, exp(-z t) * f t`. -/
private noncomputable def newman_partial (f : ℝ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..T, Complex.exp (-z * (t : ℂ)) * f t

/-- Rectangle boundary expression in Mathlib Cauchy-Goursat shape. -/
private noncomputable def newman_rect (Φ : ℂ → ℂ) (a b R : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
    - (∫ x : ℝ in a..b, Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
    + Complex.I • (∫ y : ℝ in (-R)..R, Φ ((b : ℂ) + (y : ℂ) * Complex.I))
    - Complex.I • (∫ y : ℝ in (-R)..R, Φ ((a : ℂ) + (y : ℂ) * Complex.I))

/-- Right part of the split rectangle. -/
private noncomputable def newman_JR (Φ : ℂ → ℂ) (R : ℝ) : ℂ :=
  (∫ x : ℝ in (0 : ℝ)..R, Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
    - (∫ x : ℝ in (0 : ℝ)..R, Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
    + Complex.I • (∫ y : ℝ in (-R)..R, Φ ((R : ℂ) + (y : ℂ) * Complex.I))

/-- Left part of the split rectangle (at `Re z = -δ`). -/
private noncomputable def newman_JL (Φ : ℂ → ℂ) (δ R : ℝ) : ℂ :=
  (∫ x : ℝ in (-δ)..(0 : ℝ), Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
    - (∫ x : ℝ in (-δ)..(0 : ℝ), Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
    - Complex.I • (∫ y : ℝ in (-R)..R, Φ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I))

/-- Far-left part (at `Re z = -R`). -/
private noncomputable def newman_JF (Φ : ℂ → ℂ) (R : ℝ) : ℂ :=
  (∫ x : ℝ in (-R)..(0 : ℝ), Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
    - (∫ x : ℝ in (-R)..(0 : ℝ), Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
    - Complex.I • (∫ y : ℝ in (-R)..R, Φ (((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I))

/-- Kernel bound on horizontal sides. -/
private lemma newman_kernel_norm_horizontal (R x : ℝ) (hR : 0 < R) (s : ℝ)
    (hs : s = R ∨ s = -R) :
    ‖newman_kernel R ((x : ℂ) + (s : ℂ) * Complex.I)‖ ≤ 2 * |x| / R ^ 2 := by
  have hss : s ^ 2 = R ^ 2 := by
    rcases hs with rfl | rfl
    · ring
    · ring
  have hRc : ((R : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
  have hs0 : s ≠ 0 := by
    rcases hs with rfl | rfl
    · exact ne_of_gt hR
    · exact ne_of_lt (by linarith)
  set z : ℂ := (x : ℂ) + (s : ℂ) * Complex.I with hz
  have hsim : z.im = s := by simp [hz]
  have hz0 : z ≠ 0 := by
    intro h0
    apply hs0
    have hcon := congrArg Complex.im h0
    simpa [hsim] using hcon
  have hnormz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  -- Key identity: `R^2 + z^2 = x * (x + 2 * s * I)`, since `s^2 = R^2`.
  have hcast2 : ((s : ℂ)) ^ 2 = ((R : ℂ)) ^ 2 := by
    have h : ((s ^ 2 : ℝ) : ℂ) = ((R ^ 2 : ℝ) : ℂ) := by rw [hss]
    push_cast at h
    exact h
  have h2 : ((R : ℝ) : ℂ) ^ 2 + z ^ 2
      = (x : ℂ) * ((x : ℂ) + 2 * (s : ℂ) * Complex.I) := by
    simp only [hz]
    linear_combination ((R : ℝ) : ℂ) ^ 2 * Complex.I_mul_I
      + (Complex.I * Complex.I) * hcast2
  have key : 1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2
      = (x : ℂ) * ((x : ℂ) + 2 * (s : ℂ) * Complex.I) / ((R : ℝ) : ℂ) ^ 2 := by
    have hR2 : ((R : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hRc
    field_simp
    linear_combination h2
  -- `‖x + 2 s I‖ ≤ 2 ‖z‖`, by comparing squares.
  have hsq : ‖(x : ℂ) + 2 * (s : ℂ) * Complex.I‖ ^ 2 ≤ (2 * ‖z‖) ^ 2 := by
    have e1 : ‖(x : ℂ) + 2 * (s : ℂ) * Complex.I‖ ^ 2 = x ^ 2 + (2 * s) ^ 2 := by
      have hshape : (x : ℂ) + 2 * (s : ℂ) * Complex.I
          = (x : ℂ) + ((2 * s : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [hshape, Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
    have e2 : (2 * ‖z‖) ^ 2 = 4 * (x ^ 2 + s ^ 2) := by
      have hzshape : z = (x : ℂ) + ((s : ℝ) : ℂ) * Complex.I := rfl
      rw [hzshape, Complex.norm_add_mul_I]
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [e1, e2, hss]
    nlinarith [sq_nonneg x]
  have hle : ‖(x : ℂ) + 2 * (s : ℂ) * Complex.I‖ ≤ 2 * ‖z‖ := by
    have hnn : 0 ≤ (2 : ℝ) * ‖z‖ := by positivity
    have habs : |‖(x : ℂ) + 2 * (s : ℂ) * Complex.I‖| ≤ 2 * ‖z‖ := by
      rw [← Real.norm_eq_abs]
      exact abs_le_of_sq_le_sq hsq hnn
    rwa [abs_of_nonneg (norm_nonneg _)] at habs
  -- Divide through by `‖z‖`.
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  have hnormR2 : ‖((R : ℝ) : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow]
    simp [Complex.norm_real, abs_of_pos hR]
  unfold newman_kernel
  rw [key, norm_div, norm_div, hnormR2, norm_mul, Complex.norm_real,
    div_div, div_le_iff₀ (mul_pos hR2pos hnormz)]
  have hrw : 2 * |x| / R ^ 2 * (R ^ 2 * ‖z‖) = |x| * (2 * ‖z‖) := by
    field_simp
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg x)

/-- Kernel bound on vertical sides. -/
private lemma newman_kernel_norm_vertical (R : ℝ) (hR : 0 < R) (z : ℂ)
    (hlo : R ≤ ‖z‖) (hhi : ‖z‖ ≤ 2 * R) :
    ‖newman_kernel R z‖ ≤ 3 / R := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hR2pos : (0 : ℝ) < R ^ 2 := by positivity
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlo
    linarith
  have hRc : ((R : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hRne
  have hR2 : ((R : ℝ) : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hRc
  have hnormR2 : ‖((R : ℝ) : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow]
    simp [Complex.norm_real, abs_of_pos hR]
  have hsplit : newman_kernel R z = 1 / z + z / ((R : ℝ) : ℂ) ^ 2 := by
    unfold newman_kernel
    field_simp
  have e1 : ‖(1 : ℂ) / z‖ = 1 / ‖z‖ := by rw [norm_div, norm_one]
  have e2 : ‖z / ((R : ℝ) : ℂ) ^ 2‖ = ‖z‖ / R ^ 2 := by
    rw [norm_div, hnormR2]
  have g1 : 1 / ‖z‖ ≤ 1 / R := one_div_le_one_div_of_le hR hlo
  have g2 : ‖z‖ / R ^ 2 ≤ 2 / R := by
    have hle : ‖z‖ / R ^ 2 ≤ (2 * R) / R ^ 2 :=
      (div_le_div_iff_of_pos_right hR2pos).mpr hhi
    have heq : (2 * R) / R ^ 2 = 2 / R := by
      field_simp
    rwa [heq] at hle
  calc ‖newman_kernel R z‖ = ‖(1 : ℂ) / z + z / ((R : ℝ) : ℂ) ^ 2‖ := by rw [hsplit]
    _ ≤ ‖(1 : ℂ) / z‖ + ‖z / ((R : ℝ) : ℂ) ^ 2‖ := norm_add_le _ _
    _ = 1 / ‖z‖ + ‖z‖ / R ^ 2 := by rw [e1, e2]
    _ ≤ 1 / R + 2 / R := add_le_add g1 g2
    _ = 3 / R := by ring

/-- The partial transform is entire. -/
private lemma newman_partial_differentiable (f : ℝ → ℂ) (B : ℝ)
    (hfmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (T : ℝ) (hT : 0 ≤ T) :
    Differentiable ℂ (newman_partial f T) := by
  set fT : ℝ → ℂ := Set.indicator (Set.Ioc 0 T) f with hfT
  have hfTmeas : AEStronglyMeasurable fT (volume.restrict (Set.Ioi 0)) :=
    hfmeas.indicator measurableSet_Ioc
  -- Exponential bound for the truncated function, for every half-plane.
  have hbnd : ∀ a : ℝ, ∀ t : ℝ, 0 ≤ t →
      ‖fT t‖ ≤ (B * Real.exp (|a| * T)) * Real.exp (a * t) := by
    intro a t ht
    by_cases hmem : t ∈ Set.Ioc (0 : ℝ) T
    · have hft : ‖f t‖ ≤ B := hbound t ht
      have habs : |a * t| ≤ |a| * T := by
        rw [abs_mul, abs_of_pos hmem.1]
        exact mul_le_mul_of_nonneg_left hmem.2 (abs_nonneg a)
      have hge : (0 : ℝ) ≤ |a| * T + a * t := by
        have hneg := neg_le_of_abs_le habs
        linarith
      have hexp_ge : (1 : ℝ) ≤ Real.exp (|a| * T + a * t) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr hge
      have hrewrite : fT t = f t := by
        simp only [hfT]
        exact Set.indicator_of_mem hmem f
      rw [hrewrite]
      calc ‖f t‖ ≤ B := hft
        _ = B * 1 := (mul_one B).symm
        _ ≤ B * Real.exp (|a| * T + a * t) :=
            mul_le_mul_of_nonneg_left hexp_ge hB
        _ = (B * Real.exp (|a| * T)) * Real.exp (a * t) := by
            rw [Real.exp_add]
            ring
    · have hzero : fT t = 0 := by
        simp only [hfT]
        exact Set.indicator_of_notMem hmem f
      rw [hzero, norm_zero]
      exact mul_nonneg (mul_nonneg hB (Real.exp_nonneg _)) (Real.exp_nonneg _)
  -- The Laplace transform of the truncation is the partial transform.
  have heq : laplace fT = newman_partial f T := by
    funext z
    unfold laplace newman_partial
    have hpt : ∀ t : ℝ, Complex.exp (-z * (t : ℂ)) • fT t
        = Set.indicator (Set.Ioc 0 T)
          (fun t => Complex.exp (-z * (t : ℂ)) • f t) t := by
      intro t
      by_cases hmem : t ∈ Set.Ioc (0 : ℝ) T
      · simp only [hfT, Set.indicator_of_mem hmem]
      · simp only [hfT, Set.indicator_of_notMem hmem, smul_zero]
    rw [show (∫ t : ℝ in Set.Ioi 0, Complex.exp (-z * (t : ℂ)) • fT t)
          = ∫ t : ℝ in Set.Ioi (0 : ℝ) ∩ Set.Ioc 0 T,
            Complex.exp (-z * (t : ℂ)) • f t from by
          simp_rw [hpt]
          exact MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.mpr Set.Ioc_subset_Ioi_self,
      ← intervalIntegral.integral_of_le hT]
    simp_rw [smul_eq_mul]
  rw [← heq]
  intro z
  have hkey := differentiableOn_laplace_of_norm_le_exp fT (z.re - 1)
    (B * Real.exp (|z.re - 1| * T)) hfTmeas
    (mul_nonneg hB (Real.exp_nonneg _)) (hbnd (z.re - 1))
  have hopen : IsOpen {s : ℂ | z.re - 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hmem : z ∈ {s : ℂ | z.re - 1 < s.re} := by
    change z.re - 1 < z.re
    linarith
  exact hkey.differentiableAt (hopen.mem_nhds hmem)

/-- Laplace minus partial equals the tail integral. -/
private lemma newman_laplace_sub_partial_eq_tail (f : ℝ → ℂ)
    (G : ℂ → ℂ)
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s))
    (T : ℝ) (hT : 0 ≤ T) (z : ℂ) (hz : 0 < z.re) :
    G z - newman_partial f T z
      = ∫ t : ℝ in Set.Ioi T, Complex.exp (-z * (t : ℂ)) * f t ∧
    IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * f t) (Set.Ioi T) := by
  obtain ⟨hconv, hval⟩ := hG z hz
  have hIoc : IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) • f t)
      (Set.Ioc 0 T) :=
    hconv.mono_set Set.Ioc_subset_Ioi_self
  have hIoi : IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) • f t)
      (Set.Ioi T) :=
    hconv.mono_set (Set.Ioi_subset_Ioi hT)
  have hsplit : (∫ t : ℝ in Set.Ioc 0 T ∪ Set.Ioi T,
        Complex.exp (-z * (t : ℂ)) • f t)
      = (∫ t : ℝ in Set.Ioc 0 T, Complex.exp (-z * (t : ℂ)) • f t)
        + (∫ t : ℝ in Set.Ioi T, Complex.exp (-z * (t : ℂ)) • f t) :=
    MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      hIoc hIoi
  have hlap : laplace f z
      = ∫ t : ℝ in Set.Ioi 0, Complex.exp (-z * (t : ℂ)) • f t := rfl
  have hGval : G z
      = (∫ t : ℝ in Set.Ioc 0 T, Complex.exp (-z * (t : ℂ)) • f t)
        + (∫ t : ℝ in Set.Ioi T, Complex.exp (-z * (t : ℂ)) • f t) := by
    rw [← hval, hlap, ← Set.Ioc_union_Ioi_eq_Ioi hT]
    exact hsplit
  have hpart : (∫ t : ℝ in Set.Ioc 0 T, Complex.exp (-z * (t : ℂ)) • f t)
      = newman_partial f T z := by
    unfold newman_partial
    rw [intervalIntegral.integral_of_le hT]
    simp_rw [smul_eq_mul]
  constructor
  · rw [hGval, hpart, add_sub_cancel_left]
    simp_rw [smul_eq_mul]
  · simpa only [smul_eq_mul] using hIoi

/-- Tail bound for `Re z > 0`. -/
private lemma newman_tail_bound (f : ℝ → ℂ) (B : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s))
    (T : ℝ) (hT : 0 ≤ T) (z : ℂ) (hz : 0 < z.re) :
    ‖(G z - newman_partial f T z) * Complex.exp (z * (T : ℂ))‖ ≤ B / z.re := by
  obtain ⟨htail_eq, _⟩ := newman_laplace_sub_partial_eq_tail f G hG T hT z hz
  have hneg : -z.re < 0 := by linarith
  have hg_int : IntegrableOn (fun t : ℝ => B * Real.exp (-z.re * t)) (Set.Ioi T) :=
    (integrableOn_exp_mul_Ioi hneg T).const_mul B
  -- Pointwise bound on the tail integrand.
  have hpt : ∀ t : ℝ, t ∈ Set.Ioi T →
      ‖Complex.exp (-z * (t : ℂ)) * f t‖ ≤ B * Real.exp (-z.re * t) := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_trans hT (le_of_lt ht)
    have h1 : ‖Complex.exp (-z * (t : ℂ))‖ = Real.exp (-z.re * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [norm_mul, h1]
    calc Real.exp (-z.re * t) * ‖f t‖
        ≤ Real.exp (-z.re * t) * B :=
          mul_le_mul_of_nonneg_left (hbound t ht0) (Real.exp_nonneg _)
      _ = B * Real.exp (-z.re * t) := mul_comm _ _
  have hnorm_tail : ‖∫ t : ℝ in Set.Ioi T, Complex.exp (-z * (t : ℂ)) * f t‖
      ≤ B * Real.exp (-z.re * T) / z.re := by
    have hle := MeasureTheory.norm_integral_le_of_norm_le (μ := volume.restrict (Set.Ioi T))
      (f := fun t : ℝ => Complex.exp (-z * (t : ℂ)) * f t)
      (g := fun t : ℝ => B * Real.exp (-z.re * t))
      hg_int ((ae_restrict_iff' measurableSet_Ioi).mpr
        (ae_of_all _ (fun t ht => hpt t ht)))
    have hval : (∫ t : ℝ in Set.Ioi T, B * Real.exp (-z.re * t))
        = B * Real.exp (-z.re * T) / z.re := by
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hneg T]
      field_simp
    rw [hval] at hle
    exact hle
  -- Multiply by `‖exp (z * T)‖ = exp (z.re * T)`; the exponentials cancel.
  have hexpT : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [htail_eq, norm_mul, hexpT]
  calc ‖∫ t : ℝ in Set.Ioi T, Complex.exp (-z * (t : ℂ)) * f t‖ * Real.exp (z.re * T)
      ≤ (B * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) :=
        mul_le_mul_of_nonneg_right hnorm_tail (Real.exp_nonneg _)
    _ = B / z.re := by
        have hcancel : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
          rw [← Real.exp_add]
          simp [add_comm]
        have hrw : (B * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T)
            = (B / z.re) * (Real.exp (-z.re * T) * Real.exp (z.re * T)) := by
          ring
        rw [hrw, hcancel, mul_one]

/-- Partial bound for `Re z < 0`. -/
private lemma newman_partial_bound_left (f : ℝ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (T : ℝ) (hT : 0 ≤ T) (z : ℂ) (hz : z.re < 0) :
    ‖newman_partial f T z * Complex.exp (z * (T : ℂ))‖ ≤ B / (-z.re) := by
  have hneg : (0 : ℝ) < -z.re := neg_pos.mpr hz
  have hcont : Continuous (fun t : ℝ => B * Real.exp (-z.re * t)) :=
    continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id'))
  have hbound_int : IntervalIntegrable (fun t : ℝ => B * Real.exp (-z.re * t))
      volume 0 T :=
    hcont.intervalIntegrable 0 T
  -- Pointwise bound on the partial integrand.
  have hpt : ∀ᵐ t : ℝ ∂volume, t ∈ Set.Ioc 0 T →
      ‖Complex.exp (-z * (t : ℂ)) * f t‖ ≤ B * Real.exp (-z.re * t) := by
    apply ae_of_all
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht.1
    have h1 : ‖Complex.exp (-z * (t : ℂ))‖ = Real.exp (-z.re * t) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
    rw [norm_mul, h1]
    calc Real.exp (-z.re * t) * ‖f t‖
        ≤ Real.exp (-z.re * t) * B :=
          mul_le_mul_of_nonneg_left (hbound t ht0) (Real.exp_nonneg _)
      _ = B * Real.exp (-z.re * t) := mul_comm _ _
  have h1 : ‖newman_partial f T z‖
      ≤ ∫ t : ℝ in (0 : ℝ)..T, B * Real.exp (-z.re * t) := by
    unfold newman_partial
    exact intervalIntegral.norm_integral_le_of_norm_le hT hpt hbound_int
  -- Evaluate the exponential integral by substitution.
  have hval : (∫ t : ℝ in (0 : ℝ)..T, B * Real.exp (-z.re * t))
      = B * (Real.exp (-z.re * T) - 1) / (-z.re) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left _ (ne_of_gt hneg)]
    simp only [mul_zero, integral_exp, smul_eq_mul]
    rw [Real.exp_zero]
    ring
  rw [hval] at h1
  -- Multiply by `‖exp (z * T)‖ = exp (z.re * T)` and simplify.
  have hexpT : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hcancel : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
    rw [← Real.exp_add]
    simp [add_comm]
  rw [norm_mul, hexpT]
  calc ‖newman_partial f T z‖ * Real.exp (z.re * T)
      ≤ (B * (Real.exp (-z.re * T) - 1) / (-z.re)) * Real.exp (z.re * T) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    _ = B * (1 - Real.exp (z.re * T)) / (-z.re) := by
        linear_combination B * hcancel / (-z.re)
    _ ≤ B / (-z.re) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hneg)
        calc B * (1 - Real.exp (z.re * T))
            ≤ B * 1 :=
              mul_le_mul_of_nonneg_left
                (sub_le_self 1 (le_of_lt (Real.exp_pos _))) hB
          _ = B := mul_one B

/-- A good `δ` from compactness. -/
private lemma newman_exists_delta (G : ℂ → ℂ)
    (hG : AnalyticOnNhd ℂ G {s | 0 ≤ s.re}) (R : ℝ) (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
      ∀ z : ℂ, -δ ≤ z.re → z.re ≤ R → |z.im| ≤ R → AnalyticAt ℂ G z := by
  have hU : IsOpen {z : ℂ | AnalyticAt ℂ G z} := isOpen_analyticAt ℂ G
  set K0 : Set ℂ := Set.Icc 0 R ×ℂ Set.Icc (-R) R with hK0
  have hK0c : IsCompact K0 := isCompact_Icc.reProdIm isCompact_Icc
  have hK0U : K0 ⊆ {z | AnalyticAt ℂ G z} := by
    intro z hz
    rw [hK0, Complex.mem_reProdIm] at hz
    obtain ⟨hre, -⟩ := hz
    apply hG
    change (0 : ℝ) ≤ z.re
    exact (Set.mem_Icc.mp hre).1
  obtain ⟨δ0, hδ0, hsub⟩ := hK0c.exists_thickening_subset_open hU hK0U
  have hK0ne : K0.Nonempty := by
    refine ⟨0, ?_⟩
    rw [hK0, Complex.mem_reProdIm]
    refine ⟨Set.mem_Icc.mpr ⟨le_rfl, hR.le⟩,
      Set.mem_Icc.mpr ⟨neg_nonpos.mpr hR.le, hR.le⟩⟩
  refine ⟨min (δ0 / 2) (R / 2), lt_min (by linarith) (by linarith),
    lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_⟩
  intro z hz1 hz2 hz3
  apply hsub
  rw [Metric.mem_thickening_iff_infDist_lt hK0ne]
  -- The witness in `K0` closest in real part.
  set w : ℂ := ((max z.re 0 : ℝ) : ℂ) + ((z.im : ℝ) : ℂ) * Complex.I with hw
  have hwK : w ∈ K0 := by
    rw [hK0, Complex.mem_reProdIm]
    constructor
    · have hre_w : w.re = max z.re 0 := by simp [hw]
      rw [hre_w]
      exact Set.mem_Icc.mpr ⟨le_max_right _ _,
        max_le hz2 hR.le⟩
    · have him_w : w.im = z.im := by simp [hw]
      rw [him_w]
      exact Set.mem_Icc.mpr ⟨by linarith [abs_le.mp hz3], by linarith [abs_le.mp hz3]⟩
  have hsub_eq : z - w = ((z.re - max z.re 0 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hw]
    · simp [hw]
  have hmax : |z.re - max z.re 0| ≤ min (δ0 / 2) (R / 2) := by
    rcases le_total 0 z.re with h | h
    · rw [max_eq_left h, sub_self, abs_zero]
      exact le_min (by linarith) (by linarith)
    · rw [max_eq_right h, sub_zero, abs_of_nonpos h]
      linarith
  have hdist : dist z w < δ0 := by
    rw [Complex.dist_eq, hsub_eq, Complex.norm_real]
    calc |z.re - max z.re 0| ≤ min (δ0 / 2) (R / 2) := hmax
      _ ≤ δ0 / 2 := min_le_left _ _
      _ < δ0 := by linarith
  calc Metric.infDist z K0 ≤ dist z w := Metric.infDist_le_dist_of_mem hwK
    _ < δ0 := hdist

/-- Helper: a continuous function on an open set is interval-integrable
along a segment landing in that set. -/
private lemma newman_comp_line_integrable (Ψ : ℂ → ℂ) (U : Set ℂ)
    (hΨ : ContinuousOn Ψ U) (L : ℝ → ℂ) (hL : Continuous L)
    (p q : ℝ) (hLU : ∀ t ∈ Set.uIcc p q, L t ∈ U) :
    IntervalIntegrable (fun t => Ψ (L t)) volume p q :=
  (hΨ.comp (hL.continuousOn.mono (Set.subset_univ _))
    (fun t ht => hLU t ht)).intervalIntegrable

/-- Helper: `c * (1 / L t)` is interval-integrable along a never-vanishing line. -/
private lemma newman_const_mul_line_integrable (c : ℂ) (L : ℝ → ℂ) (hL : Continuous L)
    (hL0 : ∀ t, L t ≠ 0) (p q : ℝ) :
    IntervalIntegrable (fun t => c * ((1 : ℂ) / L t)) volume p q :=
  ((continuous_const.mul (continuous_const.div hL hL0))).intervalIntegrable p q

/-- Rectangle Cauchy formula at the origin. -/
private lemma newman_rect_cauchy_zero (Φ : ℂ → ℂ) (a b R : ℝ)
    (ha : a < 0) (hb : 0 < b) (hR : 0 < R)
    (U : Set ℂ) (hU : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U)
    (hmem : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → |z.im| ≤ R → z ∈ U) :
    newman_rect (fun z => Φ z / z) a b R = 2 * Real.pi * Complex.I * Φ 0 := by
  have hab : a ≤ b := le_of_lt (lt_trans ha hb)
  have hRle : -R ≤ R := by linarith
  -- The origin lies in `U`.
  have h0U : (0 : ℂ) ∈ U :=
    hmem 0 (le_of_lt ha) (le_of_lt hb) (by simp [hR.le])
  have h0n : U ∈ 𝓝 (0 : ℂ) := hU.mem_nhds h0U
  have hΨ : DifferentiableOn ℂ (dslope Φ 0) U :=
    (Complex.differentiableOn_dslope h0n).mpr hΦ
  have hΨcont : ContinuousOn (dslope Φ 0) U := hΨ.continuousOn
  -- Cauchy-Goursat for `dslope Φ 0` on the closed rectangle.
  have hsub : (Set.Icc a b ×ℂ Set.Icc (-R) R) ⊆ U := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨hre, him⟩ := hz
    rw [Set.mem_Icc] at hre him
    exact hmem z hre.1 hre.2 (abs_le.mpr ⟨him.1, him.2⟩)
  have hH : DifferentiableOn ℂ (dslope Φ 0) (Set.Icc a b ×ℂ Set.Icc (-R) R) :=
    hΨ.mono hsub
  set zc : ℂ := ⟨a, -R⟩ with hzc
  set wc : ℂ := ⟨b, R⟩ with hwc
  have hre_zc : zc.re = a := rfl
  have him_zc : zc.im = -R := rfl
  have hre_wc : wc.re = b := rfl
  have him_wc : wc.im = R := rfl
  have H' : DifferentiableOn ℂ (dslope Φ 0)
      (Set.uIcc zc.re wc.re ×ℂ Set.uIcc zc.im wc.im) := by
    rw [hre_zc, hre_wc, him_zc, him_wc,
      Set.uIcc_of_le hab, Set.uIcc_of_le hRle]
    exact hH
  have hCG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (dslope Φ 0) zc wc H'
  rw [hre_zc, hre_wc, him_zc, him_wc] at hCG
  have hrect0 : newman_rect (dslope Φ 0) a b R = 0 := by
    unfold newman_rect
    exact hCG
  -- Splitting `Φ z / z` off the origin.
  have hdecomp : ∀ w : ℂ, w ≠ 0 →
      Φ w / w = dslope Φ 0 w + Φ 0 * (1 / w) := by
    intro w hw
    have hw0 : w - 0 ≠ 0 := by simpa using hw
    rw [dslope_of_ne Φ hw, slope_def_field, sub_zero]
    field_simp
    ring
  -- The four paths: continuity, nonvanishing, landing in `U`.
  have hhor_cont : ∀ s : ℝ,
      Continuous (fun t : ℝ => (t : ℂ) + ((s : ℝ) : ℂ) * Complex.I) := by
    intro s
    apply Continuous.add Complex.continuous_ofReal
    exact continuous_const.mul continuous_const
  have hver_cont : ∀ c : ℝ,
      Continuous (fun t : ℝ => (c : ℂ) + ((t : ℝ) : ℂ) * Complex.I) := by
    intro c
    apply Continuous.add continuous_const
    exact Complex.continuous_ofReal.mul continuous_const
  have hhor0 : ∀ s : ℝ, s ≠ 0 → ∀ t : ℝ,
      (t : ℂ) + ((s : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro s hs t ht
    apply hs
    have hcon := congrArg Complex.im ht
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add,
      Complex.zero_im] at hcon
    exact hcon
  have hver0 : ∀ c : ℝ, c ≠ 0 → ∀ t : ℝ,
      (c : ℂ) + ((t : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro c hc t ht
    apply hc
    have hcon := congrArg Complex.re ht
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
      sub_self, add_zero, Complex.zero_re] at hcon
    exact hcon
  have hhorU : ∀ s : ℝ, |s| ≤ R → ∀ t ∈ Set.uIcc a b,
      ((t : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ∈ U := by
    intro s hs t ht
    apply hmem
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        sub_self, add_zero]
      have htI : t ∈ Set.Icc a b := by
        rw [← Set.uIcc_of_le hab]
        exact ht
      exact (Set.mem_Icc.mp htI).1
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        sub_self, add_zero]
      have htI : t ∈ Set.Icc a b := by
        rw [← Set.uIcc_of_le hab]
        exact ht
      exact (Set.mem_Icc.mp htI).2
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
      exact hs
  have hverU : ∀ c : ℝ, a ≤ c → c ≤ b → ∀ t ∈ Set.uIcc (-R) R,
      ((c : ℂ) + ((t : ℝ) : ℂ) * Complex.I) ∈ U := by
    intro c hc1 hc2 t ht
    apply hmem
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        sub_self, add_zero]
      exact hc1
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        sub_self, add_zero]
      exact hc2
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
      have htI : t ∈ Set.Icc (-R) R := by
        rw [← Set.uIcc_of_le hRle]
        exact ht
      have hmem' := Set.mem_Icc.mp htI
      exact abs_le.mpr ⟨hmem'.1, hmem'.2⟩
  -- The four split integral equations.
  have hRne : (-R : ℝ) ≠ 0 := neg_ne_zero.mpr hR.ne'
  have hRne' : (R : ℝ) ≠ 0 := hR.ne'
  have hane : a ≠ 0 := ne_of_lt ha
  have hbne : b ≠ 0 := ne_of_gt hb
  have habsR : |(-R : ℝ)| ≤ R := by rw [abs_neg, abs_of_pos hR]
  have habsR' : |(R : ℝ)| ≤ R := by rw [abs_of_pos hR]
  have hintΨlo : IntervalIntegrable
      (fun x : ℝ => dslope Φ 0 ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume a b :=
    newman_comp_line_integrable _ _ hΨcont _ (hhor_cont (-R)) a b
      (hhorU (-R) habsR)
  have hintklo : IntervalIntegrable
      (fun x : ℝ => Φ 0 * ((1 : ℂ) / ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)))
      volume a b :=
    newman_const_mul_line_integrable _ _ (hhor_cont (-R)) (hhor0 (-R) hRne) a b
  have eLo : (∫ x : ℝ in a..b,
        (fun z => Φ z / z) ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in a..b, dslope Φ 0 ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        + Φ 0 * (∫ x : ℝ in a..b,
          (1 : ℂ) / ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hintΨlo hintklo]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    exact hdecomp _ (hhor0 (-R) hRne x)
  have hintΨhi : IntervalIntegrable
      (fun x : ℝ => dslope Φ 0 ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume a b :=
    newman_comp_line_integrable _ _ hΨcont _ (hhor_cont R) a b
      (hhorU R habsR')
  have hintkhi : IntervalIntegrable
      (fun x : ℝ => Φ 0 * ((1 : ℂ) / ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)))
      volume a b :=
    newman_const_mul_line_integrable _ _ (hhor_cont R) (hhor0 R hRne') a b
  have eHi : (∫ x : ℝ in a..b,
        (fun z => Φ z / z) ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      = (∫ x : ℝ in a..b, dslope Φ 0 ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
        + Φ 0 * (∫ x : ℝ in a..b,
          (1 : ℂ) / ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hintΨhi hintkhi]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    exact hdecomp _ (hhor0 R hRne' x)
  have hintΨrt : IntervalIntegrable
      (fun y : ℝ => dslope Φ 0 ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      volume (-R) R :=
    newman_comp_line_integrable _ _ hΨcont _ (hver_cont b) (-R) R
      (hverU b hab le_rfl)
  have hintkrt : IntervalIntegrable
      (fun y : ℝ => Φ 0 * ((1 : ℂ) / ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I)))
      volume (-R) R :=
    newman_const_mul_line_integrable _ _ (hver_cont b) (hver0 b hbne) (-R) R
  have eRt : (∫ y : ℝ in (-R)..R,
        (fun z => Φ z / z) ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      = (∫ y : ℝ in (-R)..R, dslope Φ 0 ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        + Φ 0 * (∫ y : ℝ in (-R)..R,
          (1 : ℂ) / ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hintΨrt hintkrt]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with y _
    exact hdecomp _ (hver0 b hbne y)
  have hintΨlf : IntervalIntegrable
      (fun y : ℝ => dslope Φ 0 ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      volume (-R) R :=
    newman_comp_line_integrable _ _ hΨcont _ (hver_cont a) (-R) R
      (hverU a le_rfl hab)
  have hintklf : IntervalIntegrable
      (fun y : ℝ => Φ 0 * ((1 : ℂ) / ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I)))
      volume (-R) R :=
    newman_const_mul_line_integrable _ _ (hver_cont a) (hver0 a hane) (-R) R
  have eLf : (∫ y : ℝ in (-R)..R,
        (fun z => Φ z / z) ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      = (∫ y : ℝ in (-R)..R, dslope Φ 0 ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        + Φ 0 * (∫ y : ℝ in (-R)..R,
          (1 : ℂ) / ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hintΨlf hintklf]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with y _
    exact hdecomp _ (hver0 a hane y)
  -- The `1 / z` rectangle is `2πi` (bridge to `PerronKernel`).
  have hperron := PerronKernel.boundary_rect_one_div ha hb hR
  rw [mul_sub] at hperron
  have hE : (∫ x : ℝ in a..b,
          (1 : ℂ) / ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        - (∫ x : ℝ in a..b,
          (1 : ℂ) / ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
        + Complex.I * (∫ y : ℝ in (-R)..R,
          (1 : ℂ) / ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        - Complex.I * (∫ y : ℝ in (-R)..R,
          (1 : ℂ) / ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        = 2 * Real.pi * Complex.I := by
    simp only [Complex.ofReal_neg]
    linear_combination hperron
  -- Assembly.
  have hΨeq : (∫ x : ℝ in a..b,
          dslope Φ 0 ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
        - (∫ x : ℝ in a..b,
          dslope Φ 0 ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
        + Complex.I * (∫ y : ℝ in (-R)..R,
          dslope Φ 0 ((b : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        - Complex.I * (∫ y : ℝ in (-R)..R,
          dslope Φ 0 ((a : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
        = 0 := by
    unfold newman_rect at hrect0
    simpa only [smul_eq_mul] using hrect0
  unfold newman_rect
  rw [eLo, eHi, eRt, eLf]
  simp only [smul_eq_mul]
  linear_combination hΨeq + Φ 0 * hE

/-- Helper: continuity of horizontal lines. -/
private lemma newman_hor_cont (s : ℝ) :
    Continuous (fun t : ℝ => (t : ℂ) + ((s : ℝ) : ℂ) * Complex.I) := by
  apply Continuous.add Complex.continuous_ofReal
  exact continuous_const.mul continuous_const

/-- Helper: continuity of vertical lines. -/
private lemma newman_ver_cont (c : ℝ) :
    Continuous (fun t : ℝ => (c : ℂ) + ((t : ℝ) : ℂ) * Complex.I) := by
  apply Continuous.add continuous_const
  exact Complex.continuous_ofReal.mul continuous_const

/-- Helper: horizontal lines with nonzero imaginary part avoid `0`. -/
private lemma newman_hor_ne (s : ℝ) (hs : s ≠ 0) (t : ℝ) :
    (t : ℂ) + ((s : ℝ) : ℂ) * Complex.I ≠ 0 := by
  intro ht
  apply hs
  have hcon := congrArg Complex.im ht
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add,
    Complex.zero_im] at hcon
  exact hcon

/-- Helper: vertical lines with nonzero real part avoid `0`. -/
private lemma newman_ver_ne (c : ℝ) (hc : c ≠ 0) (t : ℝ) :
    (c : ℂ) + ((t : ℝ) : ℂ) * Complex.I ≠ 0 := by
  intro ht
  apply hc
  have hcon := congrArg Complex.re ht
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
    sub_self, add_zero, Complex.zero_re] at hcon
  exact hcon

/-- Splitting the rectangle at `Re z = 0`. -/
private lemma newman_rect_split (Φ : ℂ → ℂ) (δ R : ℝ)
    (hlo : IntervalIntegrable (fun x : ℝ => Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume (-δ) 0)
    (hhi : IntervalIntegrable (fun x : ℝ => Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume (-δ) 0)
    (rlo : IntervalIntegrable (fun x : ℝ => Φ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume 0 R)
    (rhi : IntervalIntegrable (fun x : ℝ => Φ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      MeasureTheory.volume 0 R) :
    newman_rect Φ (-δ) R R = newman_JR Φ R + newman_JL Φ δ R := by
  unfold newman_rect newman_JR newman_JL
  rw [← intervalIntegral.integral_add_adjacent_intervals hlo rlo,
    ← intervalIntegral.integral_add_adjacent_intervals hhi rhi]
  abel

/-- Newman's integrand `F(z) = (G z - g_T z) * exp (z * T) * k_R z`. -/
private noncomputable def newman_F (f : ℝ → ℂ) (G : ℂ → ℂ) (T R : ℝ) (z : ℂ) : ℂ :=
  (G z - newman_partial f T z) * Complex.exp (z * (T : ℂ)) * newman_kernel R z

/-- The `G`-part `F_G(z) = G z * exp (z * T) * k_R z`. -/
private noncomputable def newman_FG (G : ℂ → ℂ) (T R : ℝ) (z : ℂ) : ℂ :=
  G z * Complex.exp (z * (T : ℂ)) * newman_kernel R z

/-- The `g_T`-part `F_T(z) = g_T z * exp (z * T) * k_R z`. -/
private noncomputable def newman_FT (f : ℝ → ℂ) (T R : ℝ) (z : ℂ) : ℂ :=
  newman_partial f T z * Complex.exp (z * (T : ℂ)) * newman_kernel R z

/-- Shifting the left side out to `-R`. -/
private lemma newman_left_shift (Ψ : ℂ → ℂ) (δ R : ℝ)
    (hδ : 0 < δ) (hδR : δ < R)
    (hΨ : DifferentiableOn ℂ Ψ {z | z ≠ 0}) :
    newman_JL Ψ δ R = newman_JF Ψ R := by
  have hR : (0 : ℝ) < R := lt_trans hδ hδR
  have hRne : (-R : ℝ) ≠ 0 := neg_ne_zero.mpr hR.ne'
  have hRne' : (R : ℝ) ≠ 0 := hR.ne'
  have hΨcont : ContinuousOn Ψ {z | z ≠ 0} := hΨ.continuousOn
  -- Cauchy-Goursat on `[-R, -δ] × [-R, R]`, which avoids `0`.
  have hsub : (Set.uIcc (-R) (-δ) ×ℂ Set.uIcc (-R) R) ⊆ {z | z ≠ 0} := by
    intro z hz
    rw [Complex.mem_reProdIm] at hz
    obtain ⟨hre, -⟩ := hz
    rw [Set.uIcc_of_le (show -R ≤ -δ by linarith)] at hre
    have hle : z.re ≤ -δ := (Set.mem_Icc.mp hre).2
    intro h0
    rw [h0, Complex.zero_re] at hle
    linarith
  have H : DifferentiableOn ℂ Ψ (Set.uIcc (-R) (-δ) ×ℂ Set.uIcc (-R) R) :=
    hΨ.mono hsub
  have hCG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn Ψ
    ((⟨-R, -R⟩ : ℂ)) ((⟨-δ, R⟩ : ℂ)) H
  -- Integrability for splitting the far-left horizontals at `-δ`.
  have i1 : IntervalIntegrable
      (fun x : ℝ => Ψ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume (-R) (-δ) :=
    newman_comp_line_integrable _ _ hΨcont _ (newman_hor_cont _)
      (-R) (-δ) (fun t _ => newman_hor_ne _ hRne t)
  have i2 : IntervalIntegrable
      (fun x : ℝ => Ψ ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hΨcont _ (newman_hor_cont _)
      (-δ) 0 (fun t _ => newman_hor_ne _ hRne t)
  have j1 : IntervalIntegrable
      (fun x : ℝ => Ψ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume (-R) (-δ) :=
    newman_comp_line_integrable _ _ hΨcont _ (newman_hor_cont _)
      (-R) (-δ) (fun t _ => newman_hor_ne _ hRne' t)
  have j2 : IntervalIntegrable
      (fun x : ℝ => Ψ ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hΨcont _ (newman_hor_cont _)
      (-δ) 0 (fun t _ => newman_hor_ne _ hRne' t)
  simp only [smul_eq_mul] at hCG
  unfold newman_JL newman_JF
  simp only [smul_eq_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2,
    ← intervalIntegral.integral_add_adjacent_intervals j1 j2]
  linear_combination -hCG

/-- The contour identity. -/
private lemma newman_contour_identity (f : ℝ → ℂ) (B : ℝ)
    (hfmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (R δ T : ℝ) (hδ : 0 < δ) (hδR : δ < R) (hT : 0 ≤ T)
    (hmem : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ R → |z.im| ≤ R → AnalyticAt ℂ G z) :
    2 * Real.pi * Complex.I * (G 0 - newman_partial f T 0)
      = newman_JR (newman_F f G T R) R + newman_JL (newman_FG G T R) δ R
        - newman_JF (newman_FT f T R) R := by
  have hR0 : (0 : ℝ) < R := lt_trans hδ hδR
  have hnegδ : -δ ≤ (0 : ℝ) := by linarith
  have hleδR : -δ ≤ R := by linarith
  have hR2ne : ((R : ℝ) : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast hR0.ne')
  set U : Set ℂ := {z | AnalyticAt ℂ G z} with hUdef
  have hUopen : IsOpen U := isOpen_analyticAt ℂ G
  have hmemU : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ R → |z.im| ≤ R → z ∈ U :=
    fun z h1 h2 h3 => hmem z h1 h2 h3
  -- Differentiability of the pieces.
  have hgT : Differentiable ℂ (newman_partial f T) :=
    newman_partial_differentiable f B hfmeas hB hbound T hT
  have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (z * (T : ℂ))) :=
    Complex.differentiable_exp.comp (differentiable_id.mul_const _)
  have hpoly : Differentiable ℂ (fun z : ℂ => 1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2) :=
    Differentiable.add (differentiable_const _)
      ((differentiable_id.pow 2).div (differentiable_const _) (fun _ => hR2ne))
  have hk : DifferentiableOn ℂ (newman_kernel R) {z | z ≠ 0} := by
    unfold newman_kernel
    apply DifferentiableOn.div
    · exact (Differentiable.add (differentiable_const _)
        ((differentiable_id.pow 2).div (differentiable_const _)
          (fun _ => hR2ne))).differentiableOn
    · exact differentiable_id.differentiableOn
    · intro z hz
      exact hz
  have hk_cont : ContinuousOn (newman_kernel R) {z | z ≠ 0} := hk.continuousOn
  have hGdiff : DifferentiableOn ℂ G U := by
    intro z hz
    have hza : AnalyticAt ℂ G z := hz
    exact hza.differentiableAt.differentiableWithinAt
  -- Continuity of the three integrands.
  have hFcont : ContinuousOn (newman_F f G T R) (U ∩ {z | z ≠ 0}) := by
    unfold newman_F
    exact (((hGdiff.continuousOn.mono Set.inter_subset_left).sub
      (hgT.continuous.continuousOn.mono (Set.subset_univ _))).mul
      (hexp.continuous.continuousOn.mono (Set.subset_univ _))).mul
      (hk_cont.mono Set.inter_subset_right)
  have hFGcont : ContinuousOn (newman_FG G T R) (U ∩ {z | z ≠ 0}) := by
    unfold newman_FG
    exact ((hGdiff.continuousOn.mono Set.inter_subset_left).mul
      (hexp.continuous.continuousOn.mono (Set.subset_univ _))).mul
      (hk_cont.mono Set.inter_subset_right)
  have hFTcont : ContinuousOn (newman_FT f T R) {z | z ≠ 0} := by
    unfold newman_FT
    exact ((hgT.continuous.continuousOn).mul hexp.continuous.continuousOn).mul
      hk_cont
  -- `Φ` is differentiable on `U`; identify `Φ z / z` with `F z`.
  have hΦdiff : DifferentiableOn ℂ
      (fun z => (G z - newman_partial f T z) * Complex.exp (z * (T : ℂ)) *
        (1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2)) U :=
    ((hGdiff.sub hgT.differentiableOn).mul hexp.differentiableOn).mul
      hpoly.differentiableOn
  have hΦF : (fun z => (G z - newman_partial f T z) * Complex.exp (z * (T : ℂ)) *
        (1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2) / z)
      = newman_F f G T R := by
    funext z
    unfold newman_F newman_kernel
    rw [mul_div_assoc]
  have hΦ0 : (G 0 - newman_partial f T 0) * Complex.exp ((0 : ℂ) * (T : ℂ)) *
        (1 + (0 : ℂ) ^ 2 / ((R : ℝ) : ℂ) ^ 2)
      = G 0 - newman_partial f T 0 := by
    rw [zero_mul, Complex.exp_zero]
    simp
  have hN8 := newman_rect_cauchy_zero
    (fun z => (G z - newman_partial f T z) * Complex.exp (z * (T : ℂ)) *
      (1 + z ^ 2 / ((R : ℝ) : ℂ) ^ 2)) (-δ) R R
    (by linarith) hR0 hR0 U hUopen hΦdiff hmemU
  rw [hΦF, hΦ0] at hN8
  -- Segment membership.
  have hhor_seg : ∀ x s : ℝ, -δ ≤ x → x ≤ R → |s| = R →
      ((x : ℂ) + (s : ℂ) * Complex.I) ∈ U ∩ {z | z ≠ 0} := by
    intro x s h1 h2 hs
    have hre : ((x : ℂ) + (s : ℂ) * Complex.I).re = x := by simp
    have him : ((x : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hs
      linarith
    constructor
    · have e1 : -δ ≤ ((x : ℂ) + (s : ℂ) * Complex.I).re := by
        rw [hre]
        exact h1
      have e2 : ((x : ℂ) + (s : ℂ) * Complex.I).re ≤ R := by
        rw [hre]
        exact h2
      have e3 : |((x : ℂ) + (s : ℂ) * Complex.I).im| ≤ R := by
        rw [him, hs]
      exact hmemU _ e1 e2 e3
    · change ((x : ℂ) + (s : ℂ) * Complex.I) ≠ 0
      exact newman_hor_ne s hs0 x
  have hver_seg : ∀ y : ℝ, |y| ≤ R →
      (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) ∈ U ∩ {z | z ≠ 0} := by
    intro y hy
    have hre : (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).re = -δ := by simp
    have him : (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
    have hδ0 : (-δ : ℝ) ≠ 0 := ne_of_lt (by linarith)
    constructor
    · have e1 : -δ ≤ (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).re := by
        rw [hre]
      have e2 : (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).re ≤ R := by
        rw [hre]
        linarith
      have e3 : |(((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I).im| ≤ R := by
        rw [him]
        exact hy
      exact hmemU _ e1 e2 e3
    · change (((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I) ≠ 0
      exact newman_ver_ne (-δ) hδ0 y
  have hu_lo1 : ∀ t ∈ Set.uIcc (-δ) (0 : ℝ), -δ ≤ t ∧ t ≤ R := by
    intro t ht
    rw [Set.uIcc_of_le hnegδ] at ht
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ht
    exact ⟨h1, le_trans h2 hR0.le⟩
  have hu_lo2 : ∀ t ∈ Set.uIcc (0 : ℝ) R, -δ ≤ t ∧ t ≤ R := by
    intro t ht
    rw [Set.uIcc_of_le hR0.le] at ht
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ht
    exact ⟨le_trans hnegδ h1, h2⟩
  have hu_v : ∀ t ∈ Set.uIcc (-R) R, |t| ≤ R := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith : -R ≤ R)] at ht
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp ht
    exact abs_le.mpr ⟨h1, h2⟩
  have habsRm : |(-R : ℝ)| = R := by rw [abs_neg, abs_of_pos hR0]
  have habsRp : |(R : ℝ)| = R := by rw [abs_of_pos hR0]
  -- Integrability battery.
  have intFlo1 : IntervalIntegrable
      (fun x => newman_F f G T R ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact hhor_seg t (-R) h1 h2 habsRm)
  have intFlo2 : IntervalIntegrable
      (fun x => newman_F f G T R ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume 0 R :=
    newman_comp_line_integrable _ _ hFcont _ (newman_hor_cont _)
      0 R (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo2 t ht
        exact hhor_seg t (-R) h1 h2 habsRm)
  have intFhi1 : IntervalIntegrable
      (fun x => newman_F f G T R ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact hhor_seg t R h1 h2 habsRp)
  have intFhi2 : IntervalIntegrable
      (fun x => newman_F f G T R ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume 0 R :=
    newman_comp_line_integrable _ _ hFcont _ (newman_hor_cont _)
      0 R (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo2 t ht
        exact hhor_seg t R h1 h2 habsRp)
  have intFGlo : IntervalIntegrable
      (fun x => newman_FG G T R ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFGcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact hhor_seg t (-R) h1 h2 habsRm)
  have intFGhi : IntervalIntegrable
      (fun x => newman_FG G T R ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFGcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact hhor_seg t R h1 h2 habsRp)
  have intFGv : IntervalIntegrable
      (fun y => newman_FG G T R (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      volume (-R) R :=
    newman_comp_line_integrable _ _ hFGcont _ (newman_ver_cont _)
      (-R) R (fun t ht => hver_seg t (hu_v t ht))
  have intFTlo : IntervalIntegrable
      (fun x => newman_FT f T R ((x : ℂ) + ((-R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFTcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact (hhor_seg t (-R) h1 h2 habsRm).2)
  have intFThi : IntervalIntegrable
      (fun x => newman_FT f T R ((x : ℂ) + ((R : ℝ) : ℂ) * Complex.I))
      volume (-δ) 0 :=
    newman_comp_line_integrable _ _ hFTcont _ (newman_hor_cont _)
      (-δ) 0 (fun t ht => by
        obtain ⟨h1, h2⟩ := hu_lo1 t ht
        exact (hhor_seg t R h1 h2 habsRp).2)
  have intFTv : IntervalIntegrable
      (fun y => newman_FT f T R (((-δ : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      volume (-R) R :=
    newman_comp_line_integrable _ _ hFTcont _ (newman_ver_cont _)
      (-R) R (fun t ht => (hver_seg t (hu_v t ht)).2)
  -- Split the rectangle, then `F = F_G - F_T` on the left part.
  have hN9 := newman_rect_split (newman_F f G T R) δ R
    intFlo1 intFhi1 intFlo2 intFhi2
  rw [hN9] at hN8
  have hFsub : newman_F f G T R = newman_FG G T R - newman_FT f T R := by
    funext z
    change (G z - newman_partial f T z) * Complex.exp (z * ((T : ℝ) : ℂ)) * newman_kernel R z
      = (G z * Complex.exp (z * ((T : ℝ) : ℂ)) * newman_kernel R z
        - newman_partial f T z * Complex.exp (z * ((T : ℝ) : ℂ)) * newman_kernel R z)
    ring
  have hJL : newman_JL (newman_F f G T R) δ R
      = newman_JL (newman_FG G T R) δ R - newman_JL (newman_FT f T R) δ R := by
    unfold newman_JL
    simp only [hFsub, Pi.sub_apply]
    rw [intervalIntegral.integral_sub intFGlo intFTlo,
      intervalIntegral.integral_sub intFGhi intFThi,
      intervalIntegral.integral_sub intFGv intFTv,
      smul_sub]
    abel
  rw [hJL] at hN8
  -- Move the `g_T` piece out to `-R`.
  have hFTdiff : DifferentiableOn ℂ (newman_FT f T R) {z | z ≠ 0} := by
    unfold newman_FT
    exact (hgT.mul hexp).differentiableOn.mul hk
  have hN10 := newman_left_shift (newman_FT f T R) δ R hδ hδR hFTdiff
  rw [hN10] at hN8
  linear_combination -hN8

/-- Bound for the right part `J_R(F)`. -/
private lemma newman_right_part_bound (f : ℝ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s))
    (R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T) :
    ‖newman_JR (newman_F f G T R) R‖ ≤ 10 * B / R := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  -- Pointwise bound on the horizontal sides.
  have hhor : ∀ s : ℝ, s = R ∨ s = -R → ∀ x ∈ Set.uIoc (0 : ℝ) R,
      ‖newman_F f G T R ((x : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * B / R ^ 2 := by
    intro s hs x hx
    rw [Set.uIoc_of_le hR.le] at hx
    have hx0 : (0 : ℝ) < x := (Set.mem_Ioc.mp hx).1
    have hx0' : x ≠ 0 := ne_of_gt hx0
    set z : ℂ := (x : ℂ) + ((s : ℝ) : ℂ) * Complex.I with hz
    have hre : z.re = x := by simp [hz]
    have hN5 := newman_tail_bound f B hbound G hG T hT z (by rw [hre]; exact hx0)
    rw [hre] at hN5
    have hN1 := newman_kernel_norm_horizontal R x hR s hs
    have hxabs : |x| = x := abs_of_pos hx0
    have hprod : B / x * (2 * |x| / R ^ 2) = 2 * B / R ^ 2 := by
      rw [hxabs]
      field_simp
    have hF : ‖newman_F f G T R z‖
        = ‖(G z - newman_partial f T z) * Complex.exp (z * (T : ℂ))‖
          * ‖newman_kernel R z‖ := by
      unfold newman_F
      rw [norm_mul]
    rw [hF]
    calc ‖(G z - newman_partial f T z) * Complex.exp (z * (T : ℂ))‖ * ‖newman_kernel R z‖
        ≤ (B / x) * (2 * |x| / R ^ 2) :=
          mul_le_mul hN5 hN1 (norm_nonneg _) (div_nonneg hB hx0.le)
      _ = 2 * B / R ^ 2 := hprod
  -- Pointwise bound on the right side.
  have hver : ∀ y ∈ Set.uIoc (-R) R,
      ‖newman_F f G T R (((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
        ≤ 3 * B / R ^ 2 := by
    intro y hy
    rw [Set.uIoc_of_le (by linarith : -R ≤ R)] at hy
    have hyR : |y| ≤ R := abs_le.mpr ⟨(Set.mem_Ioc.mp hy).1.le, (Set.mem_Ioc.mp hy).2⟩
    set z : ℂ := ((R : ℝ) : ℂ) + ((y : ℝ) : ℂ) * Complex.I with hz
    have hre : z.re = R := by simp [hz]
    have hN5 := newman_tail_bound f B hbound G hG T hT z (by rw [hre]; exact hR)
    rw [hre] at hN5
    have hlo : R ≤ ‖z‖ := by
      calc R = |R| := (abs_of_pos hR).symm
        _ = |z.re| := by rw [hre]
        _ ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hhi : ‖z‖ ≤ 2 * R := by
      calc ‖z‖ ≤ ‖((R : ℝ) : ℂ)‖ + ‖((y : ℝ) : ℂ) * Complex.I‖ :=
            norm_add_le _ _
        _ = |R| + |y| := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
              mul_one]
        _ ≤ R + R := by
            rw [abs_of_pos hR]
            exact add_le_add le_rfl hyR
        _ = 2 * R := by ring
    have hN2 := newman_kernel_norm_vertical R hR z hlo hhi
    have hprod : B / R * (3 / R) = 3 * B / R ^ 2 := by
      field_simp
    have hF : ‖newman_F f G T R z‖
        = ‖(G z - newman_partial f T z) * Complex.exp (z * (T : ℂ))‖
          * ‖newman_kernel R z‖ := by
      unfold newman_F
      rw [norm_mul]
    rw [hF]
    calc ‖(G z - newman_partial f T z) * Complex.exp (z * (T : ℂ))‖ * ‖newman_kernel R z‖
        ≤ (B / R) * (3 / R) :=
          mul_le_mul hN5 hN2 (norm_nonneg _) (div_nonneg hB hR.le)
      _ = 3 * B / R ^ 2 := hprod
  -- The three integral bounds.
  have hlo_int : ‖∫ x : ℝ in (0 : ℝ)..R,
        newman_F f G T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I)‖ ≤ 2 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (hhor (-R) (Or.inr rfl))
    rw [sub_zero, abs_of_pos hR] at h
    have hfin : 2 * B / R ^ 2 * R = 2 * B / R := by
      field_simp
    rwa [hfin] at h
  have hhi_int : ‖∫ x : ℝ in (0 : ℝ)..R,
        newman_F f G T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I)‖ ≤ 2 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (hhor R (Or.inl rfl))
    rw [sub_zero, abs_of_pos hR] at h
    have hfin : 2 * B / R ^ 2 * R = 2 * B / R := by
      field_simp
    rwa [hfin] at h
  have hv_int : ‖∫ y : ℝ in (-R)..R,
        newman_F f G T R ((((R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
        ≤ 6 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hver
    have hlen : |R - -R| = 2 * R := by
      rw [show (R - -R : ℝ) = 2 * R from by ring]
      exact abs_of_pos (by positivity)
    rw [hlen] at h
    have hfin : 3 * B / R ^ 2 * (2 * R) = 6 * B / R := by
      field_simp
      ring
    rwa [hfin] at h
  -- Assembly.
  have hJR : newman_JR (newman_F f G T R) R
      = (∫ x : ℝ in (0 : ℝ)..R,
          newman_F f G T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
        - (∫ x : ℝ in (0 : ℝ)..R,
          newman_F f G T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
        + Complex.I • (∫ y : ℝ in (-R)..R,
          newman_F f G T R ((((R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := rfl
  have hsmul : ∀ X : ℂ, ‖Complex.I • X‖ = ‖X‖ := fun X => by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hJR]
  calc ‖(∫ x : ℝ in (0 : ℝ)..R,
            newman_F f G T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (0 : ℝ)..R,
            newman_F f G T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
          + Complex.I • (∫ y : ℝ in (-R)..R,
            newman_F f G T R ((((R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        ≤ ‖(∫ x : ℝ in (0 : ℝ)..R,
            newman_F f G T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (0 : ℝ)..R,
            newman_F f G T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))‖
          + ‖Complex.I • (∫ y : ℝ in (-R)..R,
            newman_F f G T R ((((R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖ :=
          norm_add_le _ _
      _ ≤ ((2 * B / R) + (2 * B / R)) + (6 * B / R) := by
          rw [hsmul]
          exact (add_le_add (norm_sub_le _ _) le_rfl).trans
            (add_le_add (add_le_add hlo_int hhi_int) hv_int)
      _ = 10 * B / R := by ring

/-- Bound for the far-left part `J_F(F_T)`. -/
private lemma newman_far_left_bound (f : ℝ → ℂ) (B : ℝ)
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (R T : ℝ) (hR : 0 < R) (hT : 0 ≤ T) :
    ‖newman_JF (newman_FT f T R) R‖ ≤ 10 * B / R := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hC : (0 : ℝ) ≤ 2 * B / R ^ 2 :=
    div_nonneg (mul_nonneg (by norm_num) hB) (sq_nonneg R)
  -- Pointwise bound on the horizontal sides; the endpoint `x = 0` uses
  -- `k_R(±R·I) = 0` since it is not covered by N6.
  have hhor : ∀ s : ℝ, s = R ∨ s = -R → ∀ x ∈ Set.uIoc (-R) 0,
      ‖newman_FT f T R ((x : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ 2 * B / R ^ 2 := by
    intro s hs x hx
    rw [Set.uIoc_of_le (by linarith : -R ≤ (0 : ℝ))] at hx
    obtain ⟨hxlo, hxhi⟩ := Set.mem_Ioc.mp hx
    set z : ℂ := (x : ℂ) + ((s : ℝ) : ℂ) * Complex.I with hz
    have hre : z.re = x := by simp [hz]
    have hF : ‖newman_FT f T R z‖
        = ‖newman_partial f T z * Complex.exp (z * (T : ℂ))‖
          * ‖newman_kernel R z‖ := by
      unfold newman_FT
      rw [norm_mul]
    have hN1 := newman_kernel_norm_horizontal R x hR s hs
    by_cases hx0 : x = 0
    · subst hx0
      rw [abs_zero] at hN1
      have hk0 : ‖newman_kernel R z‖ = 0 := by
        have hle : ‖newman_kernel R z‖ ≤ 2 * 0 / R ^ 2 := hN1
        rw [show (2 : ℝ) * 0 / R ^ 2 = 0 from by ring] at hle
        exact le_antisymm hle (norm_nonneg _)
      rw [hF, hk0, mul_zero]
      exact hC
    · have hxneg : x < 0 := lt_of_le_of_ne hxhi hx0
      have hx0' : x ≠ 0 := ne_of_lt hxneg
      have hN6 := newman_partial_bound_left f B hB hbound T hT z
        (by rw [hre]; exact hxneg)
      rw [hre] at hN6
      have hxabs : |x| = -x := abs_of_neg hxneg
      have hprod : B / -x * (2 * |x| / R ^ 2) = 2 * B / R ^ 2 := by
        rw [hxabs]
        field_simp
      rw [hF]
      calc ‖newman_partial f T z * Complex.exp (z * (T : ℂ))‖ * ‖newman_kernel R z‖
          ≤ (B / -x) * (2 * |x| / R ^ 2) :=
            mul_le_mul hN6 hN1 (norm_nonneg _) (div_nonneg hB (neg_nonneg.mpr hxneg.le))
        _ = 2 * B / R ^ 2 := hprod
  -- Pointwise bound on the left side.
  have hver : ∀ y ∈ Set.uIoc (-R) R,
      ‖newman_FT f T R ((((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
        ≤ 3 * B / R ^ 2 := by
    intro y hy
    rw [Set.uIoc_of_le (by linarith : -R ≤ R)] at hy
    have hyR : |y| ≤ R := abs_le.mpr ⟨(Set.mem_Ioc.mp hy).1.le, (Set.mem_Ioc.mp hy).2⟩
    set z : ℂ := (((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I with hz
    have hre : z.re = -R := by simp [hz]
    have hnegR : z.re < 0 := by rw [hre]; linarith
    have hN6 := newman_partial_bound_left f B hB hbound T hT z hnegR
    have hRneg : -z.re = R := by rw [hre]; ring
    rw [hRneg] at hN6
    have hlo : R ≤ ‖z‖ := by
      calc R = |R| := (abs_of_pos hR).symm
        _ = |(-R : ℝ)| := by rw [abs_neg, abs_of_pos hR]
        _ = |z.re| := by rw [hre]
        _ ≤ ‖z‖ := Complex.abs_re_le_norm z
    have hhi : ‖z‖ ≤ 2 * R := by
      calc ‖z‖ ≤ ‖(((-R : ℝ)) : ℂ)‖ + ‖((y : ℝ) : ℂ) * Complex.I‖ :=
            norm_add_le _ _
        _ = |(-R : ℝ)| + |y| := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
              mul_one]
        _ ≤ R + R := by
            rw [abs_neg, abs_of_pos hR]
            exact add_le_add le_rfl hyR
        _ = 2 * R := by ring
    have hN2 := newman_kernel_norm_vertical R hR z hlo hhi
    have hprod : B / R * (3 / R) = 3 * B / R ^ 2 := by
      field_simp
    have hF : ‖newman_FT f T R z‖
        = ‖newman_partial f T z * Complex.exp (z * (T : ℂ))‖
          * ‖newman_kernel R z‖ := by
      unfold newman_FT
      rw [norm_mul]
    rw [hF]
    calc ‖newman_partial f T z * Complex.exp (z * (T : ℂ))‖ * ‖newman_kernel R z‖
        ≤ (B / R) * (3 / R) :=
          mul_le_mul hN6 hN2 (norm_nonneg _) (div_nonneg hB hR.le)
      _ = 3 * B / R ^ 2 := hprod
  -- The three integral bounds.
  have hlo_int : ‖∫ x : ℝ in (-R)..(0 : ℝ),
        newman_FT f T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I)‖ ≤ 2 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (hhor (-R) (Or.inr rfl))
    have hlen : |(0 : ℝ) - -R| = R := by
      have hrr : ((0 : ℝ) - -R) = R := by ring
      rw [hrr]
      exact abs_of_pos hR
    rw [hlen] at h
    have hfin : 2 * B / R ^ 2 * R = 2 * B / R := by
      field_simp
    rwa [hfin] at h
  have hhi_int : ‖∫ x : ℝ in (-R)..(0 : ℝ),
        newman_FT f T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I)‖ ≤ 2 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (hhor R (Or.inl rfl))
    have hlen : |(0 : ℝ) - -R| = R := by
      have hrr : ((0 : ℝ) - -R) = R := by ring
      rw [hrr]
      exact abs_of_pos hR
    rw [hlen] at h
    have hfin : 2 * B / R ^ 2 * R = 2 * B / R := by
      field_simp
    rwa [hfin] at h
  have hv_int : ‖∫ y : ℝ in (-R)..R,
        newman_FT f T R ((((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
        ≤ 6 * B / R := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hver
    have hlen : |R - -R| = 2 * R := by
      rw [show (R - -R : ℝ) = 2 * R from by ring]
      exact abs_of_pos (by positivity)
    rw [hlen] at h
    have hfin : 3 * B / R ^ 2 * (2 * R) = 6 * B / R := by
      field_simp
      ring
    rwa [hfin] at h
  -- Assembly.
  have hJF : newman_JF (newman_FT f T R) R
      = (∫ x : ℝ in (-R)..(0 : ℝ),
          newman_FT f T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
        - (∫ x : ℝ in (-R)..(0 : ℝ),
          newman_FT f T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
        - Complex.I • (∫ y : ℝ in (-R)..R,
          newman_FT f T R ((((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := rfl
  have hsmul : ∀ X : ℂ, ‖Complex.I • X‖ = ‖X‖ := fun X => by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hJF]
  calc ‖(∫ x : ℝ in (-R)..(0 : ℝ),
            newman_FT f T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (-R)..(0 : ℝ),
            newman_FT f T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
          - Complex.I • (∫ y : ℝ in (-R)..R,
            newman_FT f T R ((((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        ≤ ‖(∫ x : ℝ in (-R)..(0 : ℝ),
            newman_FT f T R ((x : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (-R)..(0 : ℝ),
            newman_FT f T R ((x : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))‖
          + ‖Complex.I • (∫ y : ℝ in (-R)..R,
            newman_FT f T R ((((-R : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖ :=
          norm_sub_le _ _
      _ ≤ ((2 * B / R) + (2 * B / R)) + (6 * B / R) := by
          rw [hsmul]
          exact (add_le_add (norm_sub_le _ _) le_rfl).trans
            (add_le_add (add_le_add hlo_int hhi_int) hv_int)
      _ = 10 * B / R := by ring

/-- Auxiliary: the `J_L(F_G)` estimate for fixed `T`, given a uniform
bound `M` for `‖G * k_R‖` on the three short segments. -/
private lemma newman_JL_FG_bound_aux (G : ℂ → ℂ) (R δ M T : ℝ)
    (hδ : 0 < δ) (hδR : δ < R) (hT : 0 < T) (hM0 : 0 ≤ M)
    (hseg1 : ∀ x ∈ Set.Icc (-δ) 0,
      ‖G (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I)
        * newman_kernel R (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I)‖ ≤ M)
    (hseg2 : ∀ x ∈ Set.Icc (-δ) 0,
      ‖G (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I)
        * newman_kernel R (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I)‖ ≤ M)
    (hseg3 : ∀ y ∈ Set.Icc (-R) R,
      ‖G ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
        * newman_kernel R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ ≤ M) :
    ‖newman_JL (newman_FG G T R) δ R‖
      ≤ 2 * M / T + 2 * R * M * Real.exp (-δ * T) := by
  have hR : (0 : ℝ) < R := lt_trans hδ hδR
  have hnegδ : -δ ≤ (0 : ℝ) := neg_nonpos.mpr hδ.le
  have hRle : -R ≤ R := by linarith
  -- Norm of `F_G` in terms of `‖G * k_R‖`.
  have hFGnorm : ∀ z : ℂ, ‖newman_FG G T R z‖
      = ‖G z * newman_kernel R z‖ * Real.exp (z.re * T) := by
    intro z
    have e1 : ‖Complex.exp (z * ((T : ℝ) : ℂ))‖ = Real.exp (z.re * T) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    simp only [newman_FG, norm_mul, e1]
    ring
  -- The exponential majorant is interval-integrable.
  have hg_cont : Continuous (fun x : ℝ => M * Real.exp (T * x)) :=
    continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id'))
  have hg_int : IntervalIntegrable (fun x : ℝ => M * Real.exp (T * x))
      volume (-δ) 0 :=
    hg_cont.intervalIntegrable _ _
  -- Exact value of the majorant integral.
  have hval : (∫ x : ℝ in (-δ)..(0 : ℝ), M * Real.exp (T * x))
      = M * (T⁻¹ * (1 - Real.exp (T * -δ))) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left _ hT.ne', smul_eq_mul]
    simp only [mul_zero, integral_exp, Real.exp_zero]
  have hTδ : T * -δ = -δ * T := by ring
  have hfin : M * (T⁻¹ * (1 - Real.exp (-δ * T))) ≤ M / T := by
    have h1 : T⁻¹ * (1 - Real.exp (-δ * T)) ≤ T⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left (sub_le_self 1 (Real.exp_nonneg _))
        (inv_nonneg.mpr hT.le)
    rw [mul_one] at h1
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h1 hM0
  -- Estimate on one horizontal side.
  have hside : ∀ s : ℝ, s = R ∨ s = -R →
      (∀ x ∈ Set.Icc (-δ) 0,
        ‖G (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)
          * newman_kernel R (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ M) →
      ‖∫ x : ℝ in (-δ)..(0 : ℝ),
        newman_FG G T R (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ M / T := by
    intro s hs hseg
    have hpt : ∀ᵐ x : ℝ ∂volume, x ∈ Set.Ioc (-δ) 0 →
        ‖newman_FG G T R (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖
          ≤ M * Real.exp (T * x) := by
      apply ae_of_all
      intro x hx
      have hxI : x ∈ Set.Icc (-δ) 0 := Set.Ioc_subset_Icc_self hx
      have hre : ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).re = x := by simp
      have h1 : ‖G (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)
          * newman_kernel R (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)‖ ≤ M :=
        hseg x hxI
      rw [hFGnorm, hre, mul_comm x T]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    have h := intervalIntegral.norm_integral_le_of_norm_le hnegδ hpt hg_int
    rw [hval, hTδ] at h
    exact le_trans h hfin
  -- Estimate on the left side.
  have hleft : ‖∫ y : ℝ in (-R)..R,
        newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
        ≤ 2 * R * M * Real.exp (-δ * T) := by
    have hpt : ∀ y ∈ Set.uIoc (-R) R,
        ‖newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
          ≤ M * Real.exp (-δ * T) := by
      intro y hy
      rw [Set.uIoc_of_le hRle] at hy
      have hyI : y ∈ Set.Icc (-R) R := Set.Ioc_subset_Icc_self hy
      have hre : (((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).re = -δ := by
        simp
      have h1 : ‖G ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
          * newman_kernel R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖ ≤ M :=
        hseg3 y hyI
      rw [hFGnorm, hre]
      exact mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    have hlen : |R - -R| = 2 * R := by
      rw [show (R - -R : ℝ) = 2 * R from by ring]
      exact abs_of_pos (by positivity)
    rw [hlen] at h
    calc ‖∫ y : ℝ in (-R)..R,
            newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)‖
          ≤ M * Real.exp (-δ * T) * (2 * R) := h
        _ = 2 * R * M * Real.exp (-δ * T) := by ring
  -- Assembly.
  have hJL : newman_JL (newman_FG G T R) δ R
      = (∫ x : ℝ in (-δ)..(0 : ℝ),
          newman_FG G T R (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
        - (∫ x : ℝ in (-δ)..(0 : ℝ),
          newman_FG G T R (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
        - Complex.I • (∫ y : ℝ in (-R)..R,
          newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)) := rfl
  have hsmul : ∀ X : ℂ, ‖Complex.I • X‖ = ‖X‖ := fun X => by
    rw [norm_smul, Complex.norm_I, one_mul]
  rw [hJL]
  calc ‖(∫ x : ℝ in (-δ)..(0 : ℝ),
            newman_FG G T R (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (-δ)..(0 : ℝ),
            newman_FG G T R (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
          - Complex.I • (∫ y : ℝ in (-R)..R,
            newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖
        ≤ ‖(∫ x : ℝ in (-δ)..(0 : ℝ),
            newman_FG G T R (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
          - (∫ x : ℝ in (-δ)..(0 : ℝ),
            newman_FG G T R (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))‖
          + ‖Complex.I • (∫ y : ℝ in (-R)..R,
            newman_FG G T R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))‖ :=
          norm_sub_le _ _
      _ ≤ (M / T + M / T) + (2 * R * M * Real.exp (-δ * T)) := by
          rw [hsmul]
          exact (add_le_add (norm_sub_le _ _) le_rfl).trans
            (add_le_add
              (add_le_add (hside (-R) (Or.inr rfl) hseg1)
                (hside R (Or.inl rfl) hseg2))
              hleft)
      _ = 2 * M / T + 2 * R * M * Real.exp (-δ * T) := by ring

/-- The uniform bound `M` for the left part, from compactness. -/
private lemma newman_left_part_bound (G : ℂ → ℂ) (R δ : ℝ) (hδ : 0 < δ) (hδR : δ < R)
    (hmem : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ R → |z.im| ≤ R → AnalyticAt ℂ G z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℝ, 0 < T →
      ‖newman_JL (newman_FG G T R) δ R‖
        ≤ 2 * M / T + 2 * R * M * Real.exp (-δ * T) := by
  have hR : (0 : ℝ) < R := lt_trans hδ hδR
  have hRne : (-R : ℝ) ≠ 0 := neg_ne_zero.mpr hR.ne'
  have hδne : (-δ : ℝ) ≠ 0 := ne_of_lt (by linarith : -δ < 0)
  have habsRm : |(-R : ℝ)| = R := by rw [abs_neg, abs_of_pos hR]
  have habsRp : |(R : ℝ)| = R := abs_of_pos hR
  -- `G` is continuous on its analyticity set; `k_R` is continuous off `0`.
  have hGcont : ContinuousOn G {z | AnalyticAt ℂ G z} := by
    intro z hz
    exact hz.continuousAt.continuousWithinAt
  have hR2ne : ((R : ℝ) : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (by exact_mod_cast hR.ne')
  have hk : DifferentiableOn ℂ (newman_kernel R) {z | z ≠ 0} := by
    unfold newman_kernel
    apply DifferentiableOn.div
    · exact (Differentiable.add (differentiable_const _)
        ((differentiable_id.pow 2).div (differentiable_const _)
          (fun _ => hR2ne))).differentiableOn
    · exact differentiable_id.differentiableOn
    · intro z hz
      exact hz
  have hk_cont : ContinuousOn (newman_kernel R) {z | z ≠ 0} := hk.continuousOn
  -- The three segments land in the analyticity set.
  have hsegU : ∀ x ∈ Set.Icc (-δ) 0, ∀ s : ℝ, |s| = R →
      (((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I) ∈ {z | AnalyticAt ℂ G z} := by
    intro x hx s hs
    obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
    have hre : ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).re = x := by simp
    have him : ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).im = s := by simp
    have e1 : -δ ≤ ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).re := by
      rw [hre]; exact hx1
    have e2 : ((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).re ≤ R := by
      rw [hre]; exact le_trans hx2 hR.le
    have e3 : |((((x : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I)).im| ≤ R := by
      rw [him, hs]
    exact hmem _ e1 e2 e3
  have hvsegU : ∀ y ∈ Set.Icc (-R) R,
      ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
        ∈ {z | AnalyticAt ℂ G z} := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := Set.mem_Icc.mp hy
    have hre : (((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).re = -δ := by simp
    have him : (((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).im = y := by simp
    have e1 : -δ ≤ (((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).re := by
      rw [hre]
    have e2 : (((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).re ≤ R := by
      rw [hre]; linarith
    have e3 : |(((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)).im| ≤ R := by
      rw [him]; exact abs_le.mpr ⟨hy1, hy2⟩
    exact hmem _ e1 e2 e3
  -- Continuity of `G * k_R` along the three segments.
  have hc1 : ContinuousOn (fun x : ℝ =>
      G (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I)
        * newman_kernel R (((x : ℝ) : ℂ) + (((-R : ℝ)) : ℂ) * Complex.I))
      (Set.Icc (-δ) 0) := by
    exact ((hGcont.comp ((newman_hor_cont (-R)).continuousOn.mono (Set.subset_univ _))
      (fun x hx => hsegU x hx (-R) habsRm)).mul
      (hk_cont.comp ((newman_hor_cont (-R)).continuousOn.mono (Set.subset_univ _))
        (fun x _ => newman_hor_ne (-R) hRne x)))
  have hc2 : ContinuousOn (fun x : ℝ =>
      G (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I)
        * newman_kernel R (((x : ℝ) : ℂ) + (((R : ℝ)) : ℂ) * Complex.I))
      (Set.Icc (-δ) 0) := by
    exact ((hGcont.comp ((newman_hor_cont R).continuousOn.mono (Set.subset_univ _))
      (fun x hx => hsegU x hx R habsRp)).mul
      (hk_cont.comp ((newman_hor_cont R).continuousOn.mono (Set.subset_univ _))
        (fun x _ => newman_hor_ne R hR.ne' x)))
  have hc3 : ContinuousOn (fun y : ℝ =>
      G ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I)
        * newman_kernel R ((((-δ : ℝ)) : ℂ) + ((y : ℝ) : ℂ) * Complex.I))
      (Set.Icc (-R) R) := by
    exact ((hGcont.comp ((newman_ver_cont (-δ)).continuousOn.mono (Set.subset_univ _))
      (fun y hy => hvsegU y hy)).mul
      (hk_cont.comp ((newman_ver_cont (-δ)).continuousOn.mono (Set.subset_univ _))
        (fun y _ => newman_ver_ne (-δ) hδne y)))
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  obtain ⟨C₃, hC₃⟩ := isCompact_Icc.exists_bound_of_continuousOn hc3
  have hM0 : (0 : ℝ) ≤ max C₁ (max C₂ (max C₃ 0)) := by
    have e1 : (0 : ℝ) ≤ max C₃ 0 := le_max_right _ _
    have e2 : max C₃ (0 : ℝ) ≤ max C₂ (max C₃ 0) := le_max_right _ _
    have e3 : max C₂ (max C₃ (0 : ℝ)) ≤ max C₁ (max C₂ (max C₃ 0)) :=
      le_max_right _ _
    exact le_trans e1 (le_trans e2 e3)
  have hC₁M : C₁ ≤ max C₁ (max C₂ (max C₃ 0)) := le_max_left _ _
  have hC₂M : C₂ ≤ max C₁ (max C₂ (max C₃ 0)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hC₃M : C₃ ≤ max C₁ (max C₂ (max C₃ 0)) :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨max C₁ (max C₂ (max C₃ 0)), hM0, fun T hT => ?_⟩
  exact newman_JL_FG_bound_aux G R δ _ T hδ hδR hT hM0
    (fun x hx => le_trans (hC₁ x hx) hC₁M)
    (fun x hx => le_trans (hC₂ x hx) hC₂M)
    (fun y hy => le_trans (hC₃ y hy) hC₃M)

/-- The Newman estimate. -/
private lemma newman_newman_estimate (f : ℝ → ℂ) (B : ℝ)
    (hfmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (hG_analytic : AnalyticOnNhd ℂ G {s | 0 ≤ s.re})
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s))
    (R : ℝ) (hR : 0 < R) :
    ∃ δ M : ℝ, 0 < δ ∧ δ < R ∧ 0 ≤ M ∧ ∀ T : ℝ, 0 < T →
      2 * Real.pi * ‖G 0 - newman_partial f T 0‖
        ≤ 20 * B / R + 2 * M / T + 2 * R * M * Real.exp (-δ * T) := by
  obtain ⟨δ, hδ, hδR, hmem⟩ := newman_exists_delta G hG_analytic R hR
  obtain ⟨M, hM0, hM⟩ := newman_left_part_bound G R δ hδ hδR hmem
  refine ⟨δ, M, hδ, hδR, hM0, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hN11 := newman_contour_identity f B hfmeas hB hbound G R δ T hδ hδR hT0 hmem
  have h12 := newman_right_part_bound f B hB hbound G hG R T hR hT0
  have h13 := newman_far_left_bound f B hB hbound R T hR hT0
  have h14 := hM T hT
  have h2 : ‖(2 : ℂ)‖ = 2 := RCLike.norm_two
  have hnorm : ‖2 * Real.pi * Complex.I * (G 0 - newman_partial f T 0)‖
      = 2 * Real.pi * ‖G 0 - newman_partial f T 0‖ := by
    rw [norm_mul, norm_mul, norm_mul, h2, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [← hnorm, hN11]
  calc ‖newman_JR (newman_F f G T R) R + newman_JL (newman_FG G T R) δ R
          - newman_JF (newman_FT f T R) R‖
        ≤ ‖newman_JR (newman_F f G T R) R‖ + ‖newman_JL (newman_FG G T R) δ R‖
          + ‖newman_JF (newman_FT f T R) R‖ := by
          exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (10 * B / R) + (2 * M / T + 2 * R * M * Real.exp (-δ * T))
          + (10 * B / R) :=
          add_le_add (add_le_add h12 h14) h13
      _ = 20 * B / R + 2 * M / T + 2 * R * M * Real.exp (-δ * T) := by ring

/-- **Newman's Tauberian theorem.** Let $f : \mathbb{R} \to \mathbb{C}$ be almost everywhere
strongly measurable on $(0, \infty)$ and bounded on $[0, \infty)$: for some real $B \ge 0$,
$|f(t)| \le B$ for all $t \ge 0$. Let $G : \mathbb{C} \to \mathbb{C}$ be analytic at every point
of the closed half-plane $\{s : \operatorname{Re} s \ge 0\}$, and suppose that for every $s$
with $\operatorname{Re} s > 0$ the Laplace transform of $f$ converges at $s$ and equals $G(s)$.
Then $\int_0^T f(t)\,dt \to G(0)$ as $T \to \infty$. -/
theorem newman_tauberian (f : ℝ → ℂ) (B : ℝ)
    (hfmeas : AEStronglyMeasurable f (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hB : 0 ≤ B) (hbound : ∀ t : ℝ, 0 ≤ t → ‖f t‖ ≤ B)
    (G : ℂ → ℂ)
    (hG_analytic : AnalyticOnNhd ℂ G {s | 0 ≤ s.re})
    (hG : ∀ s : ℂ, 0 < s.re → HasLaplace f s (G s)) :
    Filter.Tendsto (fun T : ℝ => ∫ t : ℝ in (0 : ℝ)..T, f t)
      Filter.atTop (𝓝 (G 0)) := by
  -- The partial transform at `0` is the ordinary integral.
  have hpart0 : ∀ T : ℝ, newman_partial f T 0 = ∫ t : ℝ in (0 : ℝ)..T, f t := by
    intro T
    have heq : (fun t : ℝ => Complex.exp (-(0 : ℂ) * (t : ℂ)) * f t) = f := by
      funext t
      simp only [neg_zero, zero_mul, Complex.exp_zero, one_mul]
    unfold newman_partial
    rw [heq]
  suffices hsuff : Filter.Tendsto (fun T : ℝ => newman_partial f T 0)
      Filter.atTop (𝓝 (G 0)) by
    exact Filter.Tendsto.congr hpart0 hsuff
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hπε : (0 : ℝ) < Real.pi * ε := mul_pos Real.pi_pos hε
  -- Choice of `R` making `20 * B / R < π * ε`.
  set R : ℝ := max 1 (20 * B / (Real.pi * ε) + 1) with hR
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hBR : 20 * B / R < Real.pi * ε := by
    have hRge : 20 * B / (Real.pi * ε) + 1 ≤ R := le_max_right _ _
    rw [div_lt_iff₀ hR0]
    have h1 : Real.pi * ε * (20 * B / (Real.pi * ε) + 1)
        = 20 * B + Real.pi * ε := by
      rw [mul_add, mul_div_cancel₀ _ hπε.ne', mul_one]
    have h2 : Real.pi * ε * (20 * B / (Real.pi * ε) + 1) ≤ Real.pi * ε * R :=
      mul_le_mul_of_nonneg_left hRge hπε.le
    linarith
  obtain ⟨δ, M, hδ, hδR, hM0, hest⟩ :=
    newman_newman_estimate f B hfmeas hB hbound G hG_analytic hG R hR0
  -- The `M`-terms tend to `0`.
  have hlim1 : Filter.Tendsto (fun T : ℝ => 2 * M / T) Filter.atTop (𝓝 0) := by
    have h : Filter.Tendsto (fun T : ℝ => (2 * M) * T⁻¹) Filter.atTop
        (𝓝 ((2 * M) * 0)) :=
      tendsto_const_nhds.mul tendsto_inv_atTop_zero
    rw [mul_zero] at h
    have e : (fun T : ℝ => 2 * M / T) = fun T => (2 * M) * T⁻¹ :=
      funext fun T => div_eq_mul_inv _ _
    rw [e]
    exact h
  have hδT : Filter.Tendsto (fun T : ℝ => δ * T) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hδ tendsto_id
  have hexp0 : Filter.Tendsto (fun T : ℝ => Real.exp (-(δ * T))) Filter.atTop
      (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hδT
  have hlim2 : Filter.Tendsto (fun T : ℝ => 2 * R * M * Real.exp (-δ * T))
      Filter.atTop (𝓝 0) := by
    have h : Filter.Tendsto (fun T : ℝ => (2 * R * M) * Real.exp (-(δ * T)))
        Filter.atTop (𝓝 ((2 * R * M) * 0)) :=
      tendsto_const_nhds.mul hexp0
    rw [mul_zero] at h
    have e : (fun T : ℝ => 2 * R * M * Real.exp (-δ * T))
        = fun T => (2 * R * M) * Real.exp (-(δ * T)) := by
      funext T
      rw [neg_mul]
    rw [e]
    exact h
  have hlim : Filter.Tendsto
      (fun T : ℝ => 2 * M / T + 2 * R * M * Real.exp (-δ * T))
      Filter.atTop (𝓝 (0 + 0)) :=
    hlim1.add hlim2
  rw [add_zero] at hlim
  have hev := hlim.eventually_lt_const hπε
  have hev0 : ∀ᶠ T : ℝ in Filter.atTop, 0 < T := Filter.eventually_gt_atTop 0
  have hev2 := hev.and hev0
  rw [Filter.eventually_atTop] at hev2
  obtain ⟨N', hN'⟩ := hev2
  refine ⟨max N' 1, fun T hT => ?_⟩
  have hTN : T ≥ N' := le_trans (le_max_left _ _) hT
  have hTpos : (0 : ℝ) < T :=
    lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hT)
  obtain ⟨hlt, -⟩ := hN' T hTN
  have hestT := hest T hTpos
  have h3 : 2 * Real.pi * ‖G 0 - newman_partial f T 0‖ < 2 * (Real.pi * ε) := by
    have h2 : 20 * B / R + (2 * M / T + 2 * R * M * Real.exp (-δ * T))
        < 2 * (Real.pi * ε) := by
      linarith [hBR, hlt]
    linarith [hestT, h2]
  have h4 : ‖G 0 - newman_partial f T 0‖ < ε := by
    by_contra hcon
    push Not at hcon
    have hle : 2 * Real.pi * ε ≤ 2 * Real.pi * ‖G 0 - newman_partial f T 0‖ :=
      mul_le_mul_of_nonneg_left hcon (by linarith [Real.pi_pos])
    linarith [h3, hle]
  rw [dist_eq_norm, norm_sub_rev]
  exact h4
