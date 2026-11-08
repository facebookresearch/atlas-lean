/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.TorusSobolev.Basic

@[expose] public section

noncomputable section

namespace TorusSobolev

open MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The actual integral coefficient of a single multivariate Fourier monomial. -/
theorem mFourierCoeff_monomial (m n : Frequency) :
    UnitAddTorus.mFourierCoeff (UnitAddTorus.mFourier m) n = if n = m then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin 2))) n m
  simpa only [MeasureTheory.ContinuousMap.inner_toLp, UnitAddTorus.mFourierCoeff,
    UnitAddTorus.mFourier_neg, smul_eq_mul, mul_comm] using h

/-- Integrability needed for coefficient linearity is supplied by compactness, not assumed. -/
theorem mFourierCoeff_integrable (f : C(UnitAddTorus (Fin 2), ℂ)) (n : Frequency) :
    Integrable (fun x ↦ UnitAddTorus.mFourier (-n) x * f x) :=
  ((UnitAddTorus.mFourier (-n)).continuous.mul f.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Linearity of the actual coefficient integral on continuous functions. -/
theorem mFourierCoeff_add (f g : C(UnitAddTorus (Fin 2), ℂ)) (n : Frequency) :
    UnitAddTorus.mFourierCoeff (f + g) n =
      UnitAddTorus.mFourierCoeff f n + UnitAddTorus.mFourierCoeff g n := by
  simpa only [UnitAddTorus.mFourierCoeff, ContinuousMap.add_apply, smul_eq_mul, mul_add] using
    integral_add (mFourierCoeff_integrable f n) (mFourierCoeff_integrable g n)

/-- Scalar linearity of the actual coefficient integral. -/
theorem mFourierCoeff_smul (c : ℂ) (f : C(UnitAddTorus (Fin 2), ℂ)) (n : Frequency) :
    UnitAddTorus.mFourierCoeff (c • f) n = c * UnitAddTorus.mFourierCoeff f n := by
  simp only [UnitAddTorus.mFourierCoeff, ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (UnitAddTorus.mFourier (-n) _) c]
  exact integral_const_mul _ _

/-- The physical unit frequency in coordinate `i`. -/
def axisFrequency (i : Fin 2) : Frequency := Pi.single i 1

/-- The four lowest nonzero lattice modes, with the primary's normalization. -/
def lowestShellUnit : C(UnitAddTorus (Fin 2), ℂ) :=
  (((4 * Real.pi)⁻¹ : ℝ) : ℂ) •
    ((UnitAddTorus.mFourier (axisFrequency 0) + UnitAddTorus.mFourier (-axisFrequency 0)) +
      (UnitAddTorus.mFourier (axisFrequency 1) + UnitAddTorus.mFourier (-axisFrequency 1)))

/-- An actual real continuous function on the period-`2π` torus. -/
def lowestShellWitness : C(Torus, ℝ) where
  toFun x := (lowestShellUnit (unitRescaling x)).re
  continuous_toFun := Complex.continuous_re.comp
    (lowestShellUnit.continuous.comp unitRescaling.continuous)

/-- Opposite Fourier modes make this polynomial real. -/
theorem lowestShellUnit_im_zero (x : UnitAddTorus (Fin 2)) : (lowestShellUnit x).im = 0 := by
  simp [lowestShellUnit, ContinuousMap.smul_apply, ContinuousMap.add_apply, smul_eq_mul,
    UnitAddTorus.mFourier_neg, Complex.mul_im]

/-- No arbitrary reconstruction is supplied: the representative is the actual polynomial. -/
theorem unitRepresentative_lowestShellWitness :
    unitRepresentative lowestShellWitness = lowestShellUnit := by
  ext x
  change (((lowestShellUnit (unitRescaling (unitRescaling.symm x))).re : ℝ) : ℂ) =
    lowestShellUnit x
  simp only [Homeomorph.apply_symm_apply]
  apply Complex.ext <;> simp [lowestShellUnit_im_zero]

/-- The four distinct lowest nonzero modes of the source's lattice. -/
def lowestShell : Finset Frequency := by
  classical
  exact {axisFrequency 0, -axisFrequency 0, axisFrequency 1, -axisFrequency 1}

theorem lowestShell_card : lowestShell.card = 4 := by
  norm_num [lowestShell, axisFrequency, funext_iff, Fin.forall_fin_two]

/-- The actual primary coefficients are `1/2` on four modes and zero elsewhere. -/
theorem fourierCoefficient_lowestShellWitness (k : Frequency) :
    fourierCoefficient lowestShellWitness k = if k ∈ lowestShell then (1 / 2 : ℂ) else 0 := by
  classical
  rw [fourierCoefficient, unitRepresentative_lowestShellWitness]
  unfold lowestShellUnit
  rw [mFourierCoeff_smul]
  simp only [mFourierCoeff_add, mFourierCoeff_monomial]
  have hπ : (2 * Real.pi : ℂ) * (((4 * Real.pi)⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by
    push_cast
    field_simp
    ring
  rw [← mul_assoc, hπ]
  simp only [lowestShell, Finset.mem_insert, Finset.mem_singleton]
  split_ifs <;> simp_all [axisFrequency, funext_iff, Fin.forall_fin_two]
  aesop

theorem frequencyWeight_lowestShell {k : Frequency} (hk : k ∈ lowestShell) :
    frequencyWeight k = 1 := by
  simp only [lowestShell, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    norm_num [frequencyWeight, axisFrequency, Fin.sum_univ_two]

/-- Weighted square summability of this actual finite-mode function. -/
theorem lowestShellWitness_isH2 : IsH2 lowestShellWitness := by
  classical
  apply summable_of_ne_finset_zero (s := lowestShell)
  intro k hk
  simp [fourierCoefficient_lowestShellWitness, hk]

/-- Its gradient energy, computed from the actual integral coefficients. -/
theorem gradientEnergy_lowestShellWitness : gradientEnergy lowestShellWitness = 1 := by
  classical
  unfold gradientEnergy
  rw [tsum_eq_sum (s := lowestShell)
    (fun k hk ↦ by simp [fourierCoefficient_lowestShellWitness, hk])]
  calc
    _ = ∑ _k ∈ lowestShell, (1 / 4 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [frequencyWeight_lowestShell hk, fourierCoefficient_lowestShellWitness, ite_eq_left hk]
      norm_num [Complex.norm_div]
    _ = 1 := by simp [lowestShell_card]

/-- Its Laplacian energy, with the primary's physical-frequency weights. -/
theorem laplaceEnergy_lowestShellWitness : laplaceEnergy lowestShellWitness = 1 := by
  classical
  unfold laplaceEnergy
  rw [tsum_eq_sum (s := lowestShell)
    (fun k hk ↦ by simp [fourierCoefficient_lowestShellWitness, hk])]
  calc
    _ = ∑ _k ∈ lowestShell, (1 / 4 : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [frequencyWeight_lowestShell hk, fourierCoefficient_lowestShellWitness, ite_eq_left hk]
      norm_num [Complex.norm_div]
    _ = 1 := by simp [lowestShell_card]

/-- The actual real mean is the real part of the actual zero Fourier coefficient. -/
theorem mean_eq_mFourierCoeff_zero_re (u : C(Torus, ℝ)) :
    mean u = (UnitAddTorus.mFourierCoeff (unitRepresentative u) 0).re := by
  have hμ : (volume : Measure (UnitAddTorus (Fin 2))) = unitHaar := rfl
  have h : Integrable (unitRepresentative u) := by
    simpa [UnitAddTorus.mFourier_zero] using mFourierCoeff_integrable (unitRepresentative u) 0
  simp only [mean, ← hμ, UnitAddTorus.mFourierCoeff, neg_zero,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_smul]
  simpa only [RCLike.re_to_complex, unitRepresentative, ContinuousMap.coe_mk,
    Complex.ofReal_re] using integral_re h

/-- Its zero mean is an integral calculation, not a witness field. -/
theorem mean_lowestShellWitness : mean lowestShellWitness = 0 := by
  rw [mean_eq_mFourierCoeff_zero_re, unitRepresentative_lowestShellWitness]
  unfold lowestShellUnit
  rw [mFourierCoeff_smul]
  simp only [mFourierCoeff_add, mFourierCoeff_monomial]
  norm_num [axisFrequency, funext_iff, Fin.forall_fin_two]

/-- The physical origin is taken to the unit-torus origin. -/
theorem unitRescaling_zero : unitRescaling (0 : Torus) = 0 := by
  ext i
  exact (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).map_zero

theorem mFourier_eval_zero (k : Frequency) : UnitAddTorus.mFourier k 0 = 1 := by
  simp [UnitAddTorus.mFourier]

/-- The actual point value agrees with the primary four-mode example. -/
theorem lowestShellWitness_at_zero : lowestShellWitness 0 = 1 / Real.pi := by
  change (lowestShellUnit (unitRescaling 0)).re = 1 / Real.pi
  rw [unitRescaling_zero]
  simp [lowestShellUnit, mFourier_eval_zero, smul_eq_mul]
  field_simp
  ring

/-- The positive witness is genuinely in the source's zero-mean Sobolev class. -/
theorem lowestShellWitness_isZeroMeanH2 : IsZeroMeanH2 lowestShellWitness :=
  ⟨lowestShellWitness_isH2, mean_lowestShellWitness⟩

/-- A populated positive case of the actual constrained optimization problem. -/
theorem lowestShellWitness_admissible : ConditionalAdmissible lowestShellWitness 1 :=
  ⟨lowestShellWitness_isZeroMeanH2, gradientEnergy_lowestShellWitness,
    laplaceEnergy_lowestShellWitness⟩

/-- The extended-real supremum has the standard least-upper-bound characterization. -/
theorem theta_le_iff (δ : ℝ) (b : EReal) :
    theta δ ≤ b ↔ ∀ u : C(Torus, ℝ), ConditionalAdmissible u δ → ((u 0) ^ 2 : ℝ) ≤ b := by
  simp [theta, conditionalPointValues, sSup_le_iff]

/-- The primary global domain is visible in the least-bound API. -/
theorem sharpRemainderValue_le_iff (b : EReal) :
    sharpRemainderValue ≤ b ↔ ∀ δ : ℝ, 1 ≤ δ → remainder δ ≤ b := by
  simp [sharpRemainderValue, sharpRemainderValues, sSup_le_iff]

/-- The weights are nonnegative squared integer frequencies. -/
theorem frequencyWeight_nonneg (k : Frequency) : 0 ≤ frequencyWeight k :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-- Full weighted `H²` summability supplies finite gradient energy. -/
theorem IsH2.gradient_summable {u : C(Torus, ℝ)} (h : IsH2 u) :
    Summable fun k ↦ frequencyWeight k * ‖fourierCoefficient u k‖ ^ 2 := by
  apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (frequencyWeight_nonneg k) (sq_nonneg _)) _ h
  intro k
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have := frequencyWeight_nonneg k
  nlinarith

/-- Full weighted `H²` summability supplies finite Laplacian energy. -/
theorem IsH2.laplace_summable {u : C(Torus, ℝ)} (h : IsH2 u) :
    Summable fun k ↦ frequencyWeight k ^ 2 * ‖fourierCoefficient u k‖ ^ 2 := by
  apply Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)) _ h
  intro k
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have := frequencyWeight_nonneg k
  nlinarith

/-- The canonical infinite Fourier sum evaluates the actual physical-period function. -/
theorem fourierReconstruction (u : C(Torus, ℝ))
    (h : Summable (UnitAddTorus.mFourierCoeff (unitRepresentative u))) (x : Torus) :
    HasSum (fun k ↦ (2 * Real.pi : ℂ)⁻¹ * fourierCoefficient u k *
      UnitAddTorus.mFourier k (unitRescaling x)) (u x : ℂ) := by
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  simpa [fourierCoefficient, ← mul_assoc, hπ, unitRepresentative, smul_eq_mul] using
    UnitAddTorus.hasSum_mFourier_series_apply_of_summable h (unitRescaling x)

end TorusSobolev
