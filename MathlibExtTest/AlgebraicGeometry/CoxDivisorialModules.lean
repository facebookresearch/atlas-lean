/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.CoxDivisorialModules

/-!
# Tests for the divisor-shift degree normalization

The shifted numerator of an admissible character `u` for the divisor `D`, with
`a` copies of the chart denominator, is homogeneous of degree
`[D] + a • deg(x^σ̂)`: the character's pairings vanish in the class group. For
the zero divisor and the trivial character it lies in the degree of the
`a`-th power of the denominator.
-/

open MathlibExt.AlgebraicGeometry.FiniteToricCoordinates
open MathlibExt.AlgebraicGeometry.CoxGradedSheaves
open MathlibExt.AlgebraicGeometry.CoxNormalizedSheafification
open MathlibExt.AlgebraicGeometry.CoxDivisorialModules

variable {n : ℕ} {F : FiniteFan n} (R : Rays F)

theorem sum_smul_rayDegree (f : Fin R.count → ℤ) :
    ∑ i, f i • (QuotientAddGroup.mk' (characterRayMap R).range) (Pi.single i 1) =
      QuotientAddGroup.mk' (characterRayMap R).range f := by
  classical
  simp only [← map_zsmul, ← map_sum]
  congr 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- The shifted numerator has degree `[D] + a • deg(x^σ̂)`. -/
theorem shiftedNumerator_mem (σ : Cone n) (D : InvariantDivisor R) (u : Lattice n) (a : ℕ)
    (h : AdmissibleDenominator R σ D u a) :
    shiftedNumerator R σ D u a ∈
      homogeneous R (divisorClass R D + a • denominatorDegree R σ) := by
  classical
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
  unfold shiftedNumerator
  apply MvPolynomial.isWeightedHomogeneous_monomial
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  have key : ∀ i, (((rayPairing R u i + D i +
      if rayInCone R σ i then 0 else (a : ℤ)).toNat : ℕ) : ℤ) =
      rayPairing R u i + D i + if rayInCone R σ i then 0 else (a : ℤ) :=
    fun i ↦ Int.toNat_of_nonneg (h i)
  simp only [← natCast_zsmul, key, rayDegree, divisorClass, denominatorDegree]
  have hl := sum_smul_rayDegree R
    (fun i ↦ rayPairing R u i + D i + if rayInCone R σ i then 0 else (a : ℤ))
  have hr := sum_smul_rayDegree R (fun i ↦ if rayInCone R σ i then 0 else 1)
  rw [hl]
  have hite : ∀ i, (if rayInCone R σ i then 0 else
      (QuotientAddGroup.mk' (characterRayMap R).range) (Pi.single i 1)) =
      (if rayInCone R σ i then (0 : ℤ) else 1) •
        (QuotientAddGroup.mk' (characterRayMap R).range) (Pi.single i 1) := by
    intro i
    split_ifs <;> simp
  simp only [hite, hr]
  rw [← map_zsmul, ← map_add, QuotientAddGroup.mk'_eq_mk']
  refine ⟨-characterRayMap R u, neg_mem ⟨u, rfl⟩, funext fun i ↦ ?_⟩
  simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, characterRayMap, rayPairing,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_eq_mul]
  split_ifs <;> ring

/-- For the zero divisor and the trivial character, the shifted numerator lies in
the degree of the `a`-th power of the chart denominator. -/
example (σ : Cone n) (a : ℕ) :
    shiftedNumerator R σ 0 0 a ∈ homogeneous R (a • denominatorDegree R σ) := by
  classical
  have h : AdmissibleDenominator R σ 0 0 a := by
    intro i
    simp only [rayPairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, zero_add]
    split_ifs <;> simp
  simpa [divisorClass] using shiftedNumerator_mem R σ 0 0 a h
