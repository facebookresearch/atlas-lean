/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.MarshallianDemand

@[expose] public section

/-!
# Homogeneity of degree zero of Marshallian demand (Atlas EC02.T03)

Source: J. Levin, *Consumer Theory*, Stanford Econ 202 lecture notes (2004), §2,
Proposition 1 (first part: for all `λ > 0`, `B(λp, λw) = B(p, w)`) and Proposition 3
(Homogeneity: for all `p, w` and `λ > 0`, `x(λp, λw) = x(p, w)`). Levin states these on
`ℝⁿ₊`; the canonical EC02.T01 `budgetSet` already builds nonnegativity in, so the statements
below are Levin's directly, with no separate consumption-set parameter.
-/

namespace MathlibExt.Economics.Consumer

open Matrix

/-- Levin, Proposition 1: scaling prices and wealth by the same positive factor leaves the budget
set unchanged. -/
theorem budgetSet_smul {L : Type*} [Fintype L] {t : ℝ} (ht : 0 < t)
    (p : L → ℝ) (w : ℝ) : budgetSet (t • p) (t * w) = budgetSet p w := by
  ext x
  change (0 ≤ x ∧ (t • p) ⬝ᵥ x ≤ t * w) ↔ (0 ≤ x ∧ p ⬝ᵥ x ≤ w)
  simp only [smul_dotProduct, smul_eq_mul, mul_le_mul_iff_of_pos_left ht]

/-- Levin, Proposition 3: Marshallian demand is homogeneous of degree zero in prices and wealth. -/
theorem isMarshallianDemand_smul_iff {L : Type*} [Fintype L] (u : (L → ℝ) → ℝ)
    {t : ℝ} (ht : 0 < t) (p : L → ℝ) (w : ℝ) (x : L → ℝ) :
    x ∈ marshallianDemand u (t • p) (t * w) ↔ x ∈ marshallianDemand u p w := by
  unfold marshallianDemand
  rw [budgetSet_smul ht]

end MathlibExt.Economics.Consumer
