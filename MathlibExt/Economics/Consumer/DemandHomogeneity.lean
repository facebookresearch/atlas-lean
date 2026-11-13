/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.ExpenditureDuality

@[expose] public section

/-!
# Homogeneity of degree zero of Marshallian demand (Atlas EC02.T03)

Source: J. Levin, *Consumer Theory*, Stanford Econ 202 lecture notes (2004), §2,
Proposition 1 (first part: for all `λ > 0`, `B(λp, λw) = B(p, w)`) and Proposition 3
(Homogeneity: for all `p, w` and `λ > 0`, `x(λp, λw) = x(p, w)`). Levin states these on
`ℝⁿ₊`. The statements use the shared `Economics.Consumer` API with an arbitrary
consumption set; choosing `X = {x | 0 ≤ x}` gives Levin's nonnegative-orthant case.
-/

open Matrix

namespace Economics.Consumer

/-- Positive scaling preserves the budget set for any consumption set. -/
theorem budgetSet_smul {L : Type*} [Fintype L] (X : Set (L → ℝ)) {t : ℝ}
    (ht : 0 < t) (p : L → ℝ) (w : ℝ) : budgetSet X (t • p) (t * w) = budgetSet X p w := by
  ext x
  change (x ∈ X ∧ (t • p) ⬝ᵥ x ≤ t * w) ↔ (x ∈ X ∧ p ⬝ᵥ x ≤ w)
  simp only [smul_dotProduct, smul_eq_mul, mul_le_mul_iff_of_pos_left ht]

/-- Marshallian demand is unchanged by positive scaling of prices and wealth. -/
theorem isMarshallianDemand_smul_iff {L : Type*} [Fintype L] (u : (L → ℝ) → ℝ)
    (X : Set (L → ℝ)) {t : ℝ} (ht : 0 < t) (p : L → ℝ) (w : ℝ) (x : L → ℝ) :
    IsMarshallianDemand u X (t • p) (t * w) x ↔ IsMarshallianDemand u X p w x := by
  unfold IsMarshallianDemand
  rw [budgetSet_smul X ht]

end Economics.Consumer
