/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Babak Modami
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Geometry 531

open MeasureTheory Complex ENNReal

/-!
# Exponential characters are in L^p

## References

* https://en.wikipedia.org/wiki/Fourier_transform (for `expChar_continuous`)

## References

* https://en.wikipedia.org/wiki/Fourier_transform (for `expChar_continuous`)

## References

* https://en.wikipedia.org/wiki/Fourier_transform (for `expChar_continuous`)

## References

* https://en.wikipedia.org/wiki/Fourier_transform (for `expChar_continuous`)

## References

* https://en.wikipedia.org/wiki/Fourier_transform (for `expChar_continuous`)

## References

* https://en.wikipedia.org/wiki/Fourier_transform (for `expChar_continuous`)

## References

* https://en.wikipedia.org/wiki/Fourier_transform (for `expChar_continuous`)
-/

namespace MetaMathlibExt

-- Geometry 531: Exponential characters are in L^p

noncomputable def expChar {d : ℕ} (lam x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  Complex.exp (Complex.I * ↑(2 * Real.pi * @inner ℝ _ _ lam x))

/-- Let Ω⊆ ℝᵈ have finite Lebesgue measure and λ ∈ ℝᵈ, then the function e^{2π i⟨λ,x ⟩} is in Lᵖ(Ω)
for all finite p> 0.
-/
lemma expChar_continuous {d : ℕ} (lam : EuclideanSpace ℝ (Fin d)) :
    Continuous (expChar lam) := by
  unfold expChar
  apply Continuous.cexp
  apply Continuous.mul continuous_const
  exact Complex.continuous_ofReal.comp
    (continuous_const.mul (innerSL ℝ lam).continuous)

lemma expChar_norm {d : ℕ} (lam x : EuclideanSpace ℝ (Fin d)) :
    ‖expChar lam x‖ = 1 := by
  unfold expChar
  have h : (Complex.I * ↑(2 * Real.pi * @inner ℝ _ _ lam x) : ℂ).re = 0 := by simp
  rw [Complex.norm_exp, h, Real.exp_zero]

lemma expChar_memLp {d : ℕ} (Omega : Set (EuclideanSpace ℝ (Fin d)))
    (hOmega_fin : volume Omega < ⊤)
    (lam : EuclideanSpace ℝ (Fin d))
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hp_top : p ≠ ⊤) :
    MemLp (fun x => expChar lam x) p (volume.restrict Omega) := by
  have h_enorm_one : ∀ x, ‖expChar (lam:=lam) x‖ₑ = 1 := by
    intro x; rw [enorm_eq_nnnorm]
    have hnn : ‖expChar lam x‖₊ = 1 := by
      rw [← NNReal.coe_inj]; simp [expChar_norm]
    rw [hnn, ENNReal.coe_one]
  have h_norm : eLpNorm (fun x => expChar lam x) p
      (volume.restrict Omega) < ⊤ := by
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp_top]
    · have h_eq : ∫⁻ x in Omega, ‖expChar lam x‖ₑ ^ ENNReal.toReal p
          = volume Omega := by
        have hr : ∀ x, ‖expChar lam x‖ₑ ^ ENNReal.toReal p = 1 := by
          intro x; rw [h_enorm_one, ENNReal.one_rpow]
        simp_rw [hr]; simp
      rw [h_eq]; exact hOmega_fin
    · exact (expChar_continuous lam).aestronglyMeasurable
  exact h_norm

end MetaMathlibExt

end
