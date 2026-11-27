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

public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveRangeProjection
public import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Support cutoffs of shifted positive operators

For positive `a` in a concrete von Neumann algebra, define `p_r(a)=s((a-rI)⁺)` for each real
threshold `r`, using the support projection of the positive part. This is a star projection and
satisfies `r p_r(a)≤a`.

If `a` is not bounded above by `rI`, the cutoff is nonzero. Every nonzero positive `a` therefore
has a strictly positive threshold with a nonzero cutoff. The definition and threshold inequality
allow all real `r`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped CStarAlgebra InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Support projection of a shifted positive part.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a∈M` and `r : ℝ`, put
`p_r(a)=s((a-rI)⁺)`, the support of the positive part. `positiveCutoffProjection M a
r=p_r(a)` is the orthogonal projection onto the closure of the range of `(a-rI)⁺`, as an
element of `M`. -/
def positiveCutoffProjection (M : VonNeumannAlgebra H) (a : PositiveElement M) (r : ℝ) : M :=
  letI : PartialOrder M := CStarAlgebra.spectralOrder M
  letI : LE M := (CStarAlgebra.spectralOrder M).toLE
  letI : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  positiveRangeProjection M ⟨((a : M) - algebraMap ℝ M r)⁺, CFC.posPart_nonneg _⟩

/-- **Star projection property of a positive cutoff.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a∈M` and `r : ℝ`, put
`p_r(a)=s((a-rI)⁺)`, the support of the positive part. `p_r(a)²=p_r(a)` and
`p_r(a)*=p_r(a)` for every real `r`. -/
theorem positiveCutoffProjection_isStarProjection (M : VonNeumannAlgebra H)
    (a : PositiveElement M) (r : ℝ) : IsStarProjection (positiveCutoffProjection M a r) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : LE M := (CStarAlgebra.spectralOrder M).toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  have h := positiveRangeProjection_isStarProjection M
    ⟨((a : M) - algebraMap ℝ M r)⁺, CFC.posPart_nonneg _⟩
  constructor
  · apply Subtype.val_injective
    exact h.isIdempotentElem.eq
  · apply Subtype.val_injective
    exact h.isSelfAdjoint.star_eq

/-- **Threshold inequality of the shifted positive-part support.** Let `H` be a complete
complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a∈M`
and `r : ℝ`, put `p_r(a)=s((a-rI)⁺)`, the support of the positive part. `r • p_r(a)≤a` in
the spectral order, without a positivity assumption on `r`. -/
theorem positiveCutoffProjection_threshold (M : VonNeumannAlgebra H)
    (a : PositiveElement M) (r : ℝ) :
    @LE.le M (CStarAlgebra.spectralOrder M).toLE (r • positiveCutoffProjection M a r) (a : M) := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : LE M := (CStarAlgebra.spectralOrder M).toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let d : M := (a : M) - algebraMap ℝ M r
  let c : M := d⁺
  let n : M := d⁻
  let p : M := positiveCutoffProjection M a r
  let q : M := 1 - p
  have hd : IsSelfAdjoint d :=
    (IsSelfAdjoint.of_nonneg a.property).sub ((show IsSelfAdjoint r from rfl).algebraMap M)
  have hc : 0 ≤ c := CFC.posPart_nonneg d
  have hn : 0 ≤ n := CFC.negPart_nonneg d
  have hcstar : star c = c := IsSelfAdjoint.of_nonneg hc
  have hnstar : star n = n := IsSelfAdjoint.of_nonneg hn
  have hp : IsStarProjection p := positiveCutoffProjection_isStarProjection M a r
  have hpstar : star p = p := hp.isSelfAdjoint.star_eq
  have hpc : p * c = c := positiveRangeProjection_mul_self M ⟨c, hc⟩
  have hcp : c * p = c := by
    have h := congrArg (star : M → M) hpc
    simpa only [star_mul, hpstar, hcstar] using h
  have hnc : n * c = 0 := CFC.negPart_mul_posPart d
  have hnp : n * p = 0 := mul_positiveRangeProjection_eq_zero M ⟨c, hc⟩ n hnc
  have hpn : p * n = 0 := by
    have h := congrArg (star : M → M) hnp
    simpa only [star_mul, hpstar, hnstar, star_zero] using h
  have ha : (a : M) = c - n + algebraMap ℝ M r := by
    have h := CFC.posPart_sub_negPart d hd
    change c - n = (a : M) - algebraMap ℝ M r at h
    rw [h]
    abel
  have hpa : p * (a : M) = c + r • p := by
    rw [ha, mul_add, mul_sub, hpc, hpn, sub_zero, Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, mul_one]
  have hap : (a : M) * p = c + r • p := by
    rw [ha, add_mul, sub_mul, hcp, hnp, sub_zero, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul]
  have hpap : p * (a : M) * p = c + r • p := by
    rw [hpa, add_mul, hcp, smul_mul_assoc, hp.isIdempotentElem.eq]
  have hq : q * (a : M) * q = (a : M) - (c + r • p) - (c + r • p) + (c + r • p) := by
    calc
      q * (a : M) * q = (a : M) - (a : M) * p - p * (a : M) + p * (a : M) * p := by
        simp only [q, sub_mul, mul_sub, one_mul, mul_one]
        abel
      _ = _ := by rw [hpap, hpa, hap]
  have hdecomp : (a : M) - r • p = c + q * (a : M) * q := by
    rw [hq]
    abel
  apply sub_nonneg.mp
  rw [hdecomp]
  have hqpos : 0 ≤ q * (a : M) * q := by
    simpa only [q, star_sub, star_one, hpstar] using star_left_conjugate_nonneg a.property q
  exact add_nonneg hc hqpos

/-- **Nonzero cutoff above a violated scalar bound.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive `a∈M` and `r : ℝ`, put
`p_r(a)=s((a-rI)⁺)`, the support of the positive part. if `a` is not at most `rI` in the
spectral order, then `p_r(a)≠0`. -/
theorem positiveCutoffProjection_ne_zero_of_not_le (M : VonNeumannAlgebra H)
    (a : PositiveElement M) (r : ℝ)
    (hnot : ¬ @LE.le M (CStarAlgebra.spectralOrder M).toLE (a : M) (algebraMap ℝ M r)) :
    positiveCutoffProjection M a r ≠ 0 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : LE M := (CStarAlgebra.spectralOrder M).toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let d : M := (a : M) - algebraMap ℝ M r
  let c : M := d⁺
  have hd : IsSelfAdjoint d :=
    (IsSelfAdjoint.of_nonneg a.property).sub ((show IsSelfAdjoint r from rfl).algebraMap M)
  intro hpzero
  have hpc : positiveCutoffProjection M a r * c = c :=
    positiveRangeProjection_mul_self M ⟨c, CFC.posPart_nonneg d⟩
  rw [hpzero, zero_mul] at hpc
  have hczero : d⁺ = 0 := hpc.symm
  have hnonpos : d ≤ 0 := (CFC.posPart_eq_zero_iff d hd).mp hczero
  exact hnot (sub_nonpos.mp hnonpos)

/-- **Nonzero positive operator has a nonzero positive-threshold cutoff.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. For positive
`a∈M` and `r : ℝ`, put `p_r(a)=s((a-rI)⁺)`, the support of the positive part. if `a≠0`,
there exists `t>0` with `p_t(a)≠0`. -/
theorem exists_positiveCutoffProjection_nonzero (M : VonNeumannAlgebra H)
    (a : PositiveElement M) (hne : (a : M) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ positiveCutoffProjection M a r ≠ 0 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : LE M := (CStarAlgebra.spectralOrder M).toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  have hnorm : 0 < ‖(a : M)‖ := norm_pos_iff.mpr hne
  refine ⟨‖(a : M)‖ / 2, by positivity, ?_⟩
  apply positiveCutoffProjection_ne_zero_of_not_le
  intro hle
  have h := (CStarAlgebra.norm_le_iff_le_algebraMap (a : M)
    (by positivity : 0 ≤ ‖(a : M)‖ / 2) a.property).mpr hle
  linarith

end

end VonNeumannAlgebra
