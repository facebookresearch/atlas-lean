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

public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveCutoffProjection
public import Mathlib.Analysis.CStarAlgebra.Projection

/-!
# Positive spectral cutoffs inside a bounding projection

Let positive `a` lie below a star projection `e` in a concrete von Neumann algebra. For a
strictly positive threshold `r`, the cutoff `p_r(a)=s((a-rI)⁺)` lies below `e`.

If `a≠0`, some `r>0` gives a nonzero cutoff satisfying both `p_r(a)≤e` and `r p_r(a)≤a`. These
are order and support properties on the given operator algebra.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Positive-threshold cutoff lies in the bounding projection.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a∈M`
and `r : ℝ`, put `p_r(a)=s((a-rI)⁺)`, the support of the positive part. if `e∈M` is a star
projection, `a≤e` and `r>0`, then `p_r(a)≤e`. -/
theorem positiveCutoffProjection_le_projection (M : VonNeumannAlgebra H)
    (a : PositiveElement M) (e : M) (he : IsStarProjection e) (r : ℝ) (hr : 0 < r)
    (hae : @LE.le M (CStarAlgebra.spectralOrder M).toLE (a : M) e) :
    @LE.le M (CStarAlgebra.spectralOrder M).toLE (positiveCutoffProjection M a r) e := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : LE M := (CStarAlgebra.spectralOrder M).toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let p : M := positiveCutoffProjection M a r
  have hp : IsStarProjection p := positiveCutoffProjection_isStarProjection M a r
  have hp0 : 0 ≤ p := by
    simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using star_mul_self_nonneg p
  have hscaled : r • p ≤ e := (positiveCutoffProjection_threshold M a r).trans hae
  have hproduct := (he.mul_right_and_mul_left_of_nonneg_of_le (smul_nonneg hr.le hp0) hscaled).2
  rw [mul_smul_comm] at hproduct
  have hfix : e * p = p := by
    have h := congrArg (fun z : M => r⁻¹ • z) hproduct
    simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using h
  exact (hp.le_iff_mul_eq_right he).mpr hfix

/-- **Nonzero localized cutoff with its scalar threshold.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a∈M` and `r :
ℝ`, put `p_r(a)=s((a-rI)⁺)`, the support of the positive part. if `a≠0` and `a≤e` for a
star projection `e`, there exists `t>0` with `p_t(a)≠0`, `p_t(a)≤e` and `t • p_t(a)≤a`. -/
theorem exists_positiveCutoffProjection_below_projection (M : VonNeumannAlgebra H)
    (a : PositiveElement M) (e : M) (he : IsStarProjection e)
    (hne : (a : M) ≠ 0)
    (hae : @LE.le M (CStarAlgebra.spectralOrder M).toLE (a : M) e) :
    ∃ r : ℝ, 0 < r ∧ positiveCutoffProjection M a r ≠ 0 ∧
      @LE.le M (CStarAlgebra.spectralOrder M).toLE (positiveCutoffProjection M a r) e ∧
      @LE.le M (CStarAlgebra.spectralOrder M).toLE (r • positiveCutoffProjection M a r) (a : M) := by
  obtain ⟨r, hr, hnonzero⟩ := exists_positiveCutoffProjection_nonzero M a hne
  exact ⟨r, hr, hnonzero, positiveCutoffProjection_le_projection M a e he r hr hae,
    positiveCutoffProjection_threshold M a r⟩

end

end VonNeumannAlgebra
