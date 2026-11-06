/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The denominator-cleared transposition formula and its reduction modulo three.
The actual axis formula and dyadic integrality remain separate geometric inputs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.DyadicCongruenceRing

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

private theorem matrix_nsmul_residue {n : Type*} (c : ℕ)
    (A : Matrix n n (ZMod 3)) : c • A = (c : ZMod 3) • A := by
  ext i j
  simp [nsmul_eq_mul]

/-- Conway's denominator-cleared formula reduces to I+L−L² modulo three.
No inverse of 14 is assumed in the coefficient ring; in particular 7 need not
be invertible in the dyadic ring. The rank-one term disappears modulo three. -/
theorem axisTransposition_polynomial_residue {n R : Type*}
    [Fintype n] [DecidableEq n] [CommRing R] (π : R →+* ZMod 3)
    (T P L : Matrix n n R)
    (h : (14 : ℕ) • T = (14 : ℕ) • (1 : Matrix n n R) - (24 : ℕ) • P -
      (16 : ℕ) • L + L ^ 2) : T.map π = 1 + L.map π - (L.map π) ^ 2 := by
  have hm := congrArg π.mapMatrix h
  simp only [map_add, map_sub, map_nsmul, map_one, map_pow] at hm
  rw [matrix_nsmul_residue, matrix_nsmul_residue,
    matrix_nsmul_residue, matrix_nsmul_residue] at hm
  have h14 : ((14 : ℕ) : ZMod 3) = -1 := by decide
  have h24 : ((24 : ℕ) : ZMod 3) = 0 := by decide
  have h16 : ((16 : ℕ) : ZMod 3) = 1 := by decide
  rw [h14, h24, h16, neg_one_smul, neg_one_smul, zero_smul, one_smul, sub_zero] at hm
  have hn := congrArg Neg.neg hm
  simpa only [RingHom.mapMatrix_apply, neg_neg, neg_add, neg_sub,
    sub_eq_add_neg, add_assoc] using hn

/-- Equal multiplication residues imply equal transposition residues whenever
both actual transpositions satisfy the displayed formula. -/
theorem axisTransposition_equal_residue_of_equal_multiplication {n R : Type*}
    [Fintype n] [DecidableEq n] [CommRing R] (π : R →+* ZMod 3)
    (T₁ T₂ P₁ P₂ L₁ L₂ : Matrix n n R)
    (h₁ : (14 : ℕ) • T₁ = (14 : ℕ) • (1 : Matrix n n R) - (24 : ℕ) • P₁ -
      (16 : ℕ) • L₁ + L₁ ^ 2)
    (h₂ : (14 : ℕ) • T₂ = (14 : ℕ) • (1 : Matrix n n R) - (24 : ℕ) • P₂ -
      (16 : ℕ) • L₂ + L₂ ^ 2)
    (hL : L₁.map π = L₂.map π) : T₁.map π = T₂.map π := by
  rw [axisTransposition_polynomial_residue π T₁ P₁ L₁ h₁,
    axisTransposition_polynomial_residue π T₂ P₂ L₂ h₂, hL]

/-- In a finite actual subgroup over the dyadic ring, these equal residues
force equality of the two transpositions themselves. Finiteness, integrality,
and the transposition formulas are explicit inputs. -/
theorem dyadic_axisTransposition_eq_of_equal_multiplication_residue {n : Type*}
    [Fintype n] [DecidableEq n]
    (K : Subgroup (Matrix.GeneralLinearGroup n DyadicCoefficientRing)) [Finite K]
    (T₁ T₂ : K) (P₁ P₂ L₁ L₂ : Matrix n n DyadicCoefficientRing)
    (h₁ : (14 : ℕ) • (T₁.val : Matrix n n DyadicCoefficientRing) =
      (14 : ℕ) • (1 : Matrix n n DyadicCoefficientRing) - (24 : ℕ) • P₁ -
      (16 : ℕ) • L₁ + L₁ ^ 2)
    (h₂ : (14 : ℕ) • (T₂.val : Matrix n n DyadicCoefficientRing) =
      (14 : ℕ) • (1 : Matrix n n DyadicCoefficientRing) - (24 : ℕ) • P₂ -
      (16 : ℕ) • L₂ + L₂ ^ 2)
    (hL : L₁.map dyadicReduction = L₂.map dyadicReduction) : T₁ = T₂ := by
  apply dyadic_finite_subgroup_reduction_injective K
  apply Units.ext
  exact axisTransposition_equal_residue_of_equal_multiplication dyadicReduction
    _ _ P₁ P₂ L₁ L₂ h₁ h₂ hL

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
