/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Fourier.CircleFejerCoefficients
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Actual Fejer convergence against every original L-one test function

Actual L-infinity/L-one Holder pairings have their computed uniform operator
norm bound. The normalized Fourier polynomial has the proved Fourier
coefficient limits; its pairings therefore converge on every Fourier
monomial in L-one. Stock dense Fourier span and closed convergence for an
equicontinuous family extend this to every actual L-one class. This is a
necessary proof for the source Hardy predual quotient map, not an assumed
weak-star approximation or chosen duality model.
-/

@[expose] public section
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal InnerProductSpace
namespace MathlibExt.Analysis.Fourier

/-- Actual Holder norm bound for the original circle pairing. -/
theorem circleLpPairing_norm_apply_le
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (h : Lp ℂ 1 AddCircle.haarAddCircle) :
    ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h‖ ≤ ‖f‖ * ‖h‖ := by
  let B := ContinuousLinearMap.mul ℂ ℂ
  have hI : ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h‖ ≤ ‖B.holder 1 f h‖ := by
    change ‖L1.integralCLM' ℂ (B.holder 1 f h)‖ ≤ ‖B.holder 1 f h‖
    rw [← L1.integral_eq']
    exact L1.norm_integral_le _
  have hB := B.norm_holder_apply_apply_le (r := 1) f h
  have hm : ‖B‖ * ‖f‖ * ‖h‖ ≤ ‖f‖ * ‖h‖ := by
    have he := mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℂ ℂ)
      (mul_nonneg (norm_nonneg f) (norm_nonneg h))
    simpa only [one_mul, mul_assoc] using he
  exact hI.trans (hB.trans hm)

/-- Actual normalized-circle pairing has its computed operator-norm bound. -/
theorem circleLpPairing_norm_le (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f‖ ≤ ‖f‖ :=
  (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f).opNorm_le_bound (norm_nonneg f)
      (circleLpPairing_norm_apply_le f)

/-- The actual finite Fejer polynomial as a genuine L-infinity boundary class. -/
def circleFejerLp (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (N : ℕ) : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  (circleFejerPolynomial f N).toLp ∞ AddCircle.haarAddCircle ℂ

/-- Literal boundary representative of the actual Fejer L-infinity class. -/
theorem circleFejerLp_coeFn
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) :
    (circleFejerLp f N : UnitAddCircle → ℂ) =ᵐ[AddCircle.haarAddCircle] circleFejerPolynomial f N :=
  ContinuousMap.coeFn_toLp AddCircle.haarAddCircle _

/-- Actual Fejer L-infinity norm bound follows from the actual finite polynomial and stock toLp bound. -/
theorem circleFejerLp_norm_le
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (N : ℕ) :
    ‖circleFejerLp f N‖ ≤ ‖f‖ := by
  have hC : ‖ContinuousMap.toLp (E := ℂ) ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle) ℂ‖ ≤ 1 := by
    simpa only [ENNReal.toReal_top, inv_zero, Real.rpow_zero] using
      ContinuousMap.toLp_norm_le (E := ℂ)
        (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) (p := ∞) (𝕜 := ℂ)
  have hL := (ContinuousMap.toLp (E := ℂ) ∞
    (AddCircle.haarAddCircle : Measure UnitAddCircle) ℂ).le_opNorm (circleFejerPolynomial f N)
  exact hL.trans ((mul_le_mul_of_nonneg_right hC (norm_nonneg _)).trans
    (by rw [one_mul]; exact circleFejerPolynomial_norm_le f N))

/-- Actual normalized Fejer pairings with each source L-one Fourier monomial. -/
theorem circleLpPairing_fourier
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (n : ℤ) :
    ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f (fourierLp 1 n) = fourierCoeff (f :
        UnitAddCircle → ℂ) (-n) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  change (∫ x, f x * fourierLp 1 n x ∂AddCircle.haarAddCircle) =
    ∫ x, fourier (-(-n)) x • f x ∂AddCircle.haarAddCircle
  apply integral_congr_ae
  filter_upwards [coeFn_fourierLp 1 n] with x hx
  rw [hx, neg_neg, smul_eq_mul, mul_comm]

/-- Actual Fejer pairings converge on each source L-one Fourier monomial. -/
theorem circleFejerLp_pairing_fourier_tendsto
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (n : ℤ) :
    Tendsto (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N)
        (fourierLp 1 n)) atTop
      (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f (fourierLp 1 n))) := by
  have he : ∀ N : ℕ,
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N) (fourierLp 1 n) =
        fourierCoeff (fun x : UnitAddCircle => circleFejerPolynomial f N x) (-n) := by
    intro N
    rw [circleLpPairing_fourier]
    exact congrFun (fourierCoeff_congr_ae (circleFejerLp_coeFn f N)) (-n)
  simp_rw [he, circleLpPairing_fourier]
  exact circleFejerPolynomial_fourierCoeff_tendsto f (-n)

/-- Computed uniform norm bound makes the actual Fejer functional family equicontinuous. -/
theorem circleFejerPairing_equicontinuous
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    Equicontinuous (fun N : ℕ => (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
        (circleFejerLp f N) : Lp ℂ 1 AddCircle.haarAddCircle → ℂ)) := by
  intro h₀
  apply Metric.equicontinuousAt_iff.mpr
  intro epsilon hepsilon
  refine ⟨epsilon / (‖f‖ + 1), div_pos hepsilon (by positivity), ?_⟩
  intro h hh N
  have hN : ‖((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N)‖ ≤ ‖f‖ :=
    (circleLpPairing_norm_le _).trans (circleFejerLp_norm_le f N)
  have hd : dist (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N) h₀)
      (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N) h) ≤
      ‖f‖ * dist h h₀ := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm']
    exact ((((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N)).le_opNorm
        _).trans
      (mul_le_mul_of_nonneg_right hN (norm_nonneg _))
  calc
    dist (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N) h₀)
        (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N) h)
        ≤ (‖f‖ + 1) * dist h h₀ :=
      hd.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 from zero_le_one))
        (dist_nonneg : (0 : ℝ) ≤ dist h h₀))
    _ < (‖f‖ + 1) * (epsilon / (‖f‖ + 1)) :=
      mul_lt_mul_of_pos_left hh (by positivity)
    _ = epsilon := by field_simp

/-- Actual pointwise convergence of Fejer pairings on every L-one boundary class. -/
theorem circleFejerLp_pairing_tendsto
    (f : Lp ℂ ∞ (AddCircle.haarAddCircle : Measure UnitAddCircle)) (h : Lp ℂ 1 AddCircle.haarAddCircle) :
    Tendsto (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N)
        h) atTop (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h)) := by
  let M : Submodule ℂ (Lp ℂ 1 (AddCircle.haarAddCircle : Measure UnitAddCircle)) :=
    { carrier := {h | Tendsto (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
        (circleFejerLp f N) h) atTop
        (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h))}
      zero_mem' := by
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) 0) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f 0))
        simpa only [map_zero] using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 (0 : ℂ)))
      add_mem' := by
        intro h₁ h₂ hh₁ hh₂
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) h₁) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h₁)) at hh₁
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) h₂) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h₂)) at hh₂
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) (h₁ + h₂)) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f (h₁ + h₂)))
        simpa only [map_add] using hh₁.add hh₂
      smul_mem' := by
        intro c h hh
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) h) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h)) at hh
        change Tendsto
          (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
            (circleFejerLp f N) (c • h)) atTop
          (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f (c • h)))
        simpa only [map_smul] using hh.const_smul c }
  have hclosed : IsClosed (M : Set (Lp ℂ 1 (AddCircle.haarAddCircle : Measure UnitAddCircle))) := by
    change IsClosed {h : Lp ℂ 1 (AddCircle.haarAddCircle : Measure UnitAddCircle) |
      Tendsto (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
        (circleFejerLp f N) h) atTop
        (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f h))}
    exact Equicontinuous.isClosed_setOfPred_tendsto
      (l := (atTop : Filter ℕ))
      (F := fun N : ℕ =>
        (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) (circleFejerLp f N) :
          Lp ℂ 1 (AddCircle.haarAddCircle : Measure UnitAddCircle) → ℂ))
      (f := (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f :
        Lp ℂ 1 (AddCircle.haarAddCircle : Measure UnitAddCircle) → ℂ))
      (circleFejerPairing_equicontinuous f)
      (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f).continuous
  have hspan : Submodule.span ℂ (Set.range (fourierLp 1 (T := (1 : ℝ)))) ≤ M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change Tendsto
      (fun N : ℕ => ((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1)
        (circleFejerLp f N) (fourierLp 1 n)) atTop
      (𝓝 (((ContinuousLinearMap.mul ℂ ℂ).lpPairing AddCircle.haarAddCircle ∞ 1) f (fourierLp 1 n)))
    exact circleFejerLp_pairing_fourier_tendsto f n
  have hclosure :
      (Submodule.span ℂ (Set.range (fourierLp 1 (T := (1 : ℝ))))).topologicalClosure ≤ M :=
    Submodule.topologicalClosure_minimal _ hspan hclosed
  have hdense := span_fourierLp_closure_eq_top (T := (1 : ℝ)) (p := 1) (by simp : (1 : ℝ≥0∞) ≠ ∞)
  rw [hdense] at hclosure
  change h ∈ M
  exact hclosure Submodule.mem_top

end MathlibExt.Analysis.Fourier
