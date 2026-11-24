/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianComposition
public import MathlibExt.Algebra.Polynomial.NatPowerCoefficients

/-!
# Actual rational Eulerian group-ring projectors

The exact native stable-sort/product-alphabet bijection supplies the
multiplicative polynomial-family identity. Actual natural-value polynomial
coefficient separation gives orthogonality; evaluation at one gives the
actual sum-to-unit law. Native polynomial degree gives the original
out-of-range zeros. The projector laws are consequences of these polynomial identities.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- Every original out-of-range coefficient element is the actual zero group-ring element. -/
theorem eulerianElement_outside (n i : ℕ) (hi : n < i) : eulerianElement n i = 0 := by
  classical
  unfold eulerianElement
  simp_rw [eulerianCoefficient_outside n i _ hi, MonoidAlgebra.single_zero]
  exact Finset.sum_const_zero

/-- The original finite homogeneous coefficient elements are pairwise orthogonal projectors. -/
theorem eulerianElement_mul_fin (n : ℕ) (i j : Fin (n + 1)) :
    eulerianElement n i.val * eulerianElement n j.val =
      if i = j then eulerianElement n i.val else 0 := by
  have h := Algebra.finitePowerCombination_coefficients_mul (n + 1)
    (fun i : Fin (n + 1) => eulerianElement n i.val) (by
      intro a b
      simpa only [Polynomial.finitePowerCombination, ← eulerianLambda_eq_sum] using
        eulerianLambda_mul_nat n a b)
  exact h i j

/-- The original Eulerian elements satisfy the full zero-supported projector law in every degree. -/
theorem eulerianElement_projector_laws (n : ℕ) :
    (∑ i : Fin (n + 1), eulerianElement n i.val) = 1 ∧
      ∀ i j : ℕ, eulerianElement n i * eulerianElement n j =
        if i = j then eulerianElement n i else 0 := by
  classical
  refine ⟨sum_eulerianElement n, ?_⟩
  intro i j
  by_cases hi : i ≤ n
  · by_cases hj : j ≤ n
    · simpa only [Fin.ext_iff] using eulerianElement_mul_fin n
        ⟨i, Nat.lt_succ_of_le hi⟩ ⟨j, Nat.lt_succ_of_le hj⟩
    · rw [eulerianElement_outside n j (by omega), mul_zero]
      have hne : i ≠ j := by omega
      rw [if_neg hne]
  · rw [eulerianElement_outside n i (by omega), zero_mul]
    split_ifs <;> rfl

end Equiv.Perm
