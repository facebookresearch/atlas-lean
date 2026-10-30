/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.StatisticalGenetics.FisherDecomposition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Tests for Fisher's variance decomposition: a concrete biallelic locus (complete dominance,
`p = 1/2`) with explicit `μ`, `α`, `V_G`, `V_A`, `V_D`; the boundary cases of a fixed allele
(`p = 1`: no variance) and no dominance (`d = 0`: `V_D = 0`, `Cov(FS) = Cov(PO)`); the general
theorems on these instances; and a junk value outside the frequency domain. -/

namespace MathlibExtTest.Biology.StatisticalGenetics.FisherDecomposition

open MathlibExt.Biology.StatisticalGenetics.FisherDecomposition

/-- Hardy–Weinberg frequencies sum to one. -/
theorem sum_biallelicFreq (q₁ : ℝ) : ∑ b, biallelicFreq q₁ b = 1 := by
  simp [biallelicFreq]

/-- Falconer's genotypic values are symmetric. -/
theorem biallelicValue_symm (a d : ℝ) (b c : Bool) :
    biallelicValue a d b c = biallelicValue a d c b := by
  cases b <;> cases c <;> rfl

/-- Complete dominance (`a = d = 1`) at `p = q = 1/2`: genotypic values `1, 1, -1` with
frequencies `1/4, 1/2, 1/4`, so `μ = 1/2` and `V_G = 3/4`. -/
example : meanValue (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 1 / 2 ∧
    genVar (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 3 / 4 := by
  constructor <;>
    norm_num [meanValue, genVar, biallelicFreq, biallelicValue, Fintype.sum_bool]

/-- Same locus: average effects `α₁ = 1/2`, `α₂ = -1/2`, `V_A = 1/2`, `V_D = 1/4`, and indeed
`V_G = 3/4 = V_A + V_D`. -/
example : avgEffect (biallelicFreq (1 / 2)) (biallelicValue 1 1) true = 1 / 2 ∧
    avgEffect (biallelicFreq (1 / 2)) (biallelicValue 1 1) false = -1 / 2 ∧
    addVar (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 1 / 2 ∧
    domVar (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 1 / 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    norm_num [avgEffect, meanValue, addVar, domVar, domDev, biallelicFreq, biallelicValue,
      Fintype.sum_bool]

/-- The closed forms agree: `2pq(a + d(q - p))² = 1/2` and `(2pqd)² = 1/4`. -/
example : addVar (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 1 / 2 ∧
    domVar (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 1 / 4 := by
  rw [addVar_biallelic, domVar_biallelic]; norm_num

/-- Covariances of relatives on the same locus: parent–offspring `1/4`, half sibs `1/8`, full
sibs `1/4 + 1/16 = 5/16`. -/
example : covParentOffspring (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 1 / 4 ∧
    covHalfSibs (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 1 / 8 ∧
    covFullSibs (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 5 / 16 := by
  have hA : addVar (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 1 / 2 := by
    rw [addVar_biallelic]; norm_num
  have hD : domVar (biallelicFreq (1 / 2)) (biallelicValue 1 1) = 1 / 4 := by
    rw [domVar_biallelic]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [covParentOffspring_eq (sum_biallelicFreq _) (biallelicValue_symm _ _), hA]; norm_num
  · rw [covHalfSibs_eq (sum_biallelicFreq _), hA]; norm_num
  · rw [covFullSibs_eq (sum_biallelicFreq _) (biallelicValue_symm _ _), hA, hD]; norm_num

/-- Boundary: a fixed allele (`p = 1`) carries no genetic variance. -/
example (a d : ℝ) : addVar (biallelicFreq 1) (biallelicValue a d) = 0 ∧
    domVar (biallelicFreq 1) (biallelicValue a d) = 0 := by
  rw [addVar_biallelic, domVar_biallelic]; norm_num

/-- Boundary: no dominance (`d = 0`) gives `V_D = 0`, so full sibs and parent–offspring pairs
have the same covariance `V_A / 2`. -/
example (q₁ a : ℝ) :
    covFullSibs (biallelicFreq q₁) (biallelicValue a 0) =
      covParentOffspring (biallelicFreq q₁) (biallelicValue a 0) := by
  rw [covFullSibs_eq (sum_biallelicFreq _) (biallelicValue_symm _ _),
    covParentOffspring_eq (sum_biallelicFreq _) (biallelicValue_symm _ _), domVar_biallelic]
  ring

/-- The least-squares property on the concrete locus: fitting `0 + 0 + 0` leaves a larger
error (`∑ p p G² = 1`) than the residual error (`V_D = 1/4`) of the optimal additive fitted
genotypic value `μ + α i + α j`. -/
example : domVar (biallelicFreq (1 / 2)) (biallelicValue 1 1) ≤
    ∑ i, ∑ j, biallelicFreq (1 / 2) i * biallelicFreq (1 / 2) j *
      (biallelicValue 1 1 i j - 0 - 0 - 0) ^ 2 :=
  domVar_le_sum_sq (fun b => by cases b <;> norm_num [biallelicFreq]) (sum_biallelicFreq _)
    (biallelicValue_symm _ _) 0 0

/-- Junk value outside the frequency domain: the definitions are total, and for "frequencies"
`(2, -1)` (summing to one but negative) the biallelic formula still evaluates, to
`V_A = 2 · 2 · (-1) · (a + d(-1 - 2))² ≤ 0`, which is not a variance. -/
example : addVar (biallelicFreq 2) (biallelicValue 1 0) = -4 := by
  rw [addVar_biallelic]; norm_num

end MathlibExtTest.Biology.StatisticalGenetics.FisherDecomposition
