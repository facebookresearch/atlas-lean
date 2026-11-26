/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Matrix.Mul

/-!
# Matched-filter SNR quotient bound

For a real positive-definite covariance `R`, signal `s ≠ 0` and
weight `w ≠ 0`, the matched-filter signal-to-noise quotient
`(w ⬝ᵥ s)² / (w ⬝ᵥ R *ᵥ w)` is at most the whitened energy
`s ⬝ᵥ R⁻¹ *ᵥ s`, with equality exactly when `w` is a nonzero
multiple of the matched weight `R⁻¹ *ᵥ s`. This is the
positive-definite Cauchy--Schwarz inequality specialized to the
matched filter. The zero-signal case is included; concrete `R = diag(1, 4)`
validation fixtures and the indefinite counterexample live in the
test module.
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.Matrix.MatchedSNRQuotient

open _root_.Matrix

/-- The matched-filter quotient `(wᵀs)^2 / (wᵀRw)` of weight `w` and signal `s`, with
`x / 0 = 0`. When `R` is the noise covariance and `wᵀRw > 0` it is the output SNR. -/
noncomputable def matchedSNR {ι : Type} [Fintype ι] (R : Matrix ι ι ℝ) (s w : ι → ℝ) : ℝ :=
  (w ⬝ᵥ s) ^ 2 / (w ⬝ᵥ R *ᵥ w)

/-- Nonzero denominator: for positive definite `R` and `w ≠ 0`, `0 < wᵀRw`. -/
theorem quadForm_pos_of_ne_zero {ι : Type} [Fintype ι] (R : Matrix ι ι ℝ)
    (hR : R.PosDef) (w : ι → ℝ) (hw : w ≠ 0) :
    0 < w ⬝ᵥ R *ᵥ w := by
  simpa using hR.dotProduct_mulVec_pos hw

/-- The whitened signal energy `sᵀR⁻¹s` is positive for positive definite `R` and
`s ≠ 0`. -/
theorem inv_quadForm_pos_of_ne_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (hR : R.PosDef) (s : ι → ℝ) (hs : s ≠ 0) :
    0 < s ⬝ᵥ R⁻¹ *ᵥ s := by
  simpa using (Matrix.PosDef.inv hR).dotProduct_mulVec_pos hs

/-- Specialized positive-definite Cauchy-Schwarz:
`(wᵀs)^2 ≤ (sᵀR⁻¹s) (wᵀRw)` for positive definite `R`. -/
theorem sq_dotProduct_le_inv_quadForm_mul_quadForm {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (hR : R.PosDef) (s w : ι → ℝ) :
    (w ⬝ᵥ s) ^ 2 ≤ (s ⬝ᵥ R⁻¹ *ᵥ s) * (w ⬝ᵥ R *ᵥ w) := by
  have hU : IsUnit R.det := (isUnit_iff_isUnit_det R).mp hR.isUnit
  have hRR : R * R⁻¹ = 1 := mul_nonsing_inv R hU
  have hcancel : R *ᵥ (R⁻¹ *ᵥ s) = s := by
    rw [mulVec_mulVec, hRR, one_mulVec]
  have hsymm : ∀ x y : ι → ℝ, x ⬝ᵥ R *ᵥ y = y ⬝ᵥ R *ᵥ x := fun x y => by
    simpa using hR.1.star_dotProduct_mulVec_comm x y
  have hRs : (R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ w = w ⬝ᵥ s := by
    rw [hsymm, hcancel]
  have hRRs : (R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ (R⁻¹ *ᵥ s) = s ⬝ᵥ R⁻¹ *ᵥ s := by
    rw [hcancel, dotProduct_comm]
  have h2 : ((R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ w) * ((R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ w)
      ≤ ((R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ (R⁻¹ *ᵥ s)) * (w ⬝ᵥ R *ᵥ w) := by
    simpa using hR.star_dotProduct_mulVec_mul_le (R⁻¹ *ᵥ s) w
  rw [hRs, hRRs, ← pow_two] at h2
  exact h2

/-- **Matched-filter SNR bound.** For real positive definite `R`, `s ≠ 0` and `w ≠ 0`,
`(wᵀs)^2 / (wᵀRw) ≤ sᵀR⁻¹s`. -/
theorem matchedSNR_le_dotProduct_inv_mulVec {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (hR : R.PosDef) (s w : ι → ℝ) (hs : s ≠ 0) (hw : w ≠ 0) :
    matchedSNR R s w ≤ s ⬝ᵥ R⁻¹ *ᵥ s := by
  have hd : 0 < w ⬝ᵥ R *ᵥ w := quadForm_pos_of_ne_zero _ hR _ hw
  have h := sq_dotProduct_le_inv_quadForm_mul_quadForm _ hR s w
  show (w ⬝ᵥ s) ^ 2 / (w ⬝ᵥ R *ᵥ w) ≤ s ⬝ᵥ R⁻¹ *ᵥ s
  rw [div_le_iff₀ hd]
  exact h

/-- Every nonzero multiple `c • R⁻¹ s` of the whitened matched filter attains the bound
`sᵀR⁻¹s`, for either sign of `c`. -/
theorem matchedSNR_inv_mulVec_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (hR : R.PosDef) (s : ι → ℝ) (hs : s ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    matchedSNR R s (c • R⁻¹ *ᵥ s) = s ⬝ᵥ R⁻¹ *ᵥ s := by
  have hU : IsUnit R.det := (isUnit_iff_isUnit_det R).mp hR.isUnit
  have hRR : R * R⁻¹ = 1 := mul_nonsing_inv R hU
  have hcancel : R *ᵥ (R⁻¹ *ᵥ s) = s := by
    rw [mulVec_mulVec, hRR, one_mulVec]
  have he : 0 < s ⬝ᵥ R⁻¹ *ᵥ s := inv_quadForm_pos_of_ne_zero _ hR _ hs
  have he' : s ⬝ᵥ R⁻¹ *ᵥ s ≠ 0 := ne_of_gt he
  have hm1 : (R⁻¹ *ᵥ s) ⬝ᵥ s = s ⬝ᵥ R⁻¹ *ᵥ s := dotProduct_comm _ _
  have hm2 : (R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ (R⁻¹ *ᵥ s) = s ⬝ᵥ R⁻¹ *ᵥ s := by
    rw [hcancel, dotProduct_comm]
  have hden : (c • R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ (c • R⁻¹ *ᵥ s)
      = c * (c * (s ⬝ᵥ R⁻¹ *ᵥ s)) := by
    simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, hm2]
  have hne : c * (c * (s ⬝ᵥ R⁻¹ *ᵥ s)) ≠ 0 := mul_ne_zero hc (mul_ne_zero hc he')
  have hden0 : (c • R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ (c • R⁻¹ *ᵥ s) ≠ 0 := by
    rw [hden]
    exact hne
  have hnum : (c • R⁻¹ *ᵥ s) ⬝ᵥ s = c * (s ⬝ᵥ R⁻¹ *ᵥ s) := by
    simp only [smul_dotProduct, smul_eq_mul, hm1]
  show ((c • R⁻¹ *ᵥ s) ⬝ᵥ s) ^ 2 / ((c • R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ (c • R⁻¹ *ᵥ s))
      = s ⬝ᵥ R⁻¹ *ᵥ s
  rw [div_eq_iff hden0, hnum, hden]
  ring

/-- **Equality case of the matched-filter bound.** For real positive definite `R`,
`s ≠ 0` and `w ≠ 0`, the SNR equals `sᵀR⁻¹s` exactly when `w = c • R⁻¹ s` for some
`c ≠ 0`. -/
theorem matchedSNR_eq_dotProduct_inv_mulVec_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (hR : R.PosDef) (s w : ι → ℝ) (hs : s ≠ 0) (hw : w ≠ 0) :
    matchedSNR R s w = s ⬝ᵥ R⁻¹ *ᵥ s ↔ ∃ c : ℝ, c ≠ 0 ∧ w = c • R⁻¹ *ᵥ s := by
  have hU : IsUnit R.det := (isUnit_iff_isUnit_det R).mp hR.isUnit
  have hRR : R * R⁻¹ = 1 := mul_nonsing_inv R hU
  have hcancel : R *ᵥ (R⁻¹ *ᵥ s) = s := by
    rw [mulVec_mulVec, hRR, one_mulVec]
  have hsymm : ∀ x y : ι → ℝ, x ⬝ᵥ R *ᵥ y = y ⬝ᵥ R *ᵥ x := fun x y => by
    simpa using hR.1.star_dotProduct_mulVec_comm x y
  have he : 0 < s ⬝ᵥ R⁻¹ *ᵥ s := inv_quadForm_pos_of_ne_zero _ hR _ hs
  have hd : 0 < w ⬝ᵥ R *ᵥ w := quadForm_pos_of_ne_zero _ hR _ hw
  have he' : s ⬝ᵥ R⁻¹ *ᵥ s ≠ 0 := ne_of_gt he
  have hd' : w ⬝ᵥ R *ᵥ w ≠ 0 := ne_of_gt hd
  have hRs : (R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ w = w ⬝ᵥ s := by
    rw [hsymm, hcancel]
  have hRs' : w ⬝ᵥ R *ᵥ (R⁻¹ *ᵥ s) = w ⬝ᵥ s := by
    rw [hcancel]
  have hRRs : (R⁻¹ *ᵥ s) ⬝ᵥ R *ᵥ (R⁻¹ *ᵥ s) = s ⬝ᵥ R⁻¹ *ᵥ s := by
    rw [hcancel, dotProduct_comm]
  constructor
  · intro h
    have h2 : (w ⬝ᵥ s) ^ 2 = (s ⬝ᵥ R⁻¹ *ᵥ s) * (w ⬝ᵥ R *ᵥ w) :=
      (div_eq_iff hd').mp h
    have h2m : (w ⬝ᵥ s) * (w ⬝ᵥ s) = (s ⬝ᵥ R⁻¹ *ᵥ s) * (w ⬝ᵥ R *ᵥ w) := by
      rw [← pow_two]
      exact h2
    have hfact : ((s ⬝ᵥ R⁻¹ *ᵥ s) • w - (w ⬝ᵥ s) • (R⁻¹ *ᵥ s)) ⬝ᵥ R *ᵥ
          ((s ⬝ᵥ R⁻¹ *ᵥ s) • w - (w ⬝ᵥ s) • (R⁻¹ *ᵥ s))
        = (s ⬝ᵥ R⁻¹ *ᵥ s) * ((s ⬝ᵥ R⁻¹ *ᵥ s) * (w ⬝ᵥ R *ᵥ w)
          - (w ⬝ᵥ s) * (w ⬝ᵥ s)) := by
      simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
        smul_dotProduct, dotProduct_smul, smul_eq_mul, hRs, hRs', hRRs]
      ring
    have hres : ((s ⬝ᵥ R⁻¹ *ᵥ s) • w - (w ⬝ᵥ s) • (R⁻¹ *ᵥ s)) ⬝ᵥ R *ᵥ
        ((s ⬝ᵥ R⁻¹ *ᵥ s) • w - (w ⬝ᵥ s) • (R⁻¹ *ᵥ s)) = 0 := by
      rw [hfact, h2m]
      ring
    have hv0 : (s ⬝ᵥ R⁻¹ *ᵥ s) • w - (w ⬝ᵥ s) • (R⁻¹ *ᵥ s) = 0 := by
      by_contra hne
      have hpos : ((s ⬝ᵥ R⁻¹ *ᵥ s) • w - (w ⬝ᵥ s) • (R⁻¹ *ᵥ s)) ⬝ᵥ R *ᵥ
          ((s ⬝ᵥ R⁻¹ *ᵥ s) • w - (w ⬝ᵥ s) • (R⁻¹ *ᵥ s)) > 0 := by
        simpa using hR.dotProduct_mulVec_pos hne
      rw [hres] at hpos
      exact lt_irrefl 0 hpos
    have hweq : (s ⬝ᵥ R⁻¹ *ᵥ s) • w = (w ⬝ᵥ s) • (R⁻¹ *ᵥ s) := sub_eq_zero.mp hv0
    have hK : (w ⬝ᵥ s) ≠ 0 := by
      intro hcon
      rw [hcon, show (0:ℝ) ^ 2 = 0 from zero_pow two_ne_zero] at h2
      have hpos : 0 < (s ⬝ᵥ R⁻¹ *ᵥ s) * (w ⬝ᵥ R *ᵥ w) := mul_pos he hd
      rw [← h2] at hpos
      exact lt_irrefl 0 hpos
    refine ⟨(s ⬝ᵥ R⁻¹ *ᵥ s)⁻¹ * (w ⬝ᵥ s), mul_ne_zero (inv_ne_zero he') hK, ?_⟩
    have hsm : (s ⬝ᵥ R⁻¹ *ᵥ s)⁻¹ • ((s ⬝ᵥ R⁻¹ *ᵥ s) • w) = w := by
      rw [smul_smul, inv_mul_cancel₀ he', one_smul]
    calc w = (s ⬝ᵥ R⁻¹ *ᵥ s)⁻¹ • ((s ⬝ᵥ R⁻¹ *ᵥ s) • w) := hsm.symm
      _ = (s ⬝ᵥ R⁻¹ *ᵥ s)⁻¹ • ((w ⬝ᵥ s) • (R⁻¹ *ᵥ s)) := by rw [hweq]
      _ = ((s ⬝ᵥ R⁻¹ *ᵥ s)⁻¹ * (w ⬝ᵥ s)) • (R⁻¹ *ᵥ s) := by rw [smul_smul]
  · rintro ⟨c, hc, rfl⟩
    exact matchedSNR_inv_mulVec_smul _ hR _ hs _ hc

/-- **Zero signal.** For `s = 0`, every nonzero weight has zero SNR, using `x / 0 = 0`
when `wᵀRw = 0` (for instance `R = 0`). -/
theorem matchedSNR_zero_signal {ι : Type} [Fintype ι] (R : Matrix ι ι ℝ)
    (w : ι → ℝ) (hw : w ≠ 0) :
    matchedSNR R 0 w = 0 := by
  show (w ⬝ᵥ (0 : ι → ℝ)) ^ 2 / (w ⬝ᵥ R *ᵥ w) = 0
  rw [dotProduct_zero, show (0:ℝ) ^ 2 = 0 from zero_pow two_ne_zero, zero_div]

/-- Boundary `w = 0`: the quotient is the totalized `0 / 0 = 0`. -/
theorem matchedSNR_zero_weight {ι : Type} [Fintype ι] (R : Matrix ι ι ℝ) (s : ι → ℝ) :
    matchedSNR R s 0 = 0 := by
  show ((0 : ι → ℝ) ⬝ᵥ s) ^ 2 / ((0 : ι → ℝ) ⬝ᵥ R *ᵥ (0 : ι → ℝ)) = 0
  rw [zero_dotProduct, show (0:ℝ) ^ 2 = 0 from zero_pow two_ne_zero, zero_div]

end MathlibExt.LinearAlgebra.Matrix.MatchedSNRQuotient
