/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianProjectors
public import MathlibExt.Combinatorics.Perm.EulerianShuffleMultiplication
public import MathlibExt.Algebra.Polynomial.NatInterpolation

/-!
# Rational convolution of Eulerian elements

The family `eulerianLambda n a = ∑ i, a^i eₙⁱ` satisfies parameter
multiplication under composition and respects signed shuffle products.
Orthogonal Eulerian projectors give composition, while finite shuffle
fibers and polynomial interpolation give shuffle multiplicativity.

For a positive integer `m`, the signed lambda operation is
`(-1)^(m - 1)` times this convolution family. This parameter sign is not
extended to rational parameters.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- Actual rational convolution parameters multiply under group-ring composition. -/
theorem eulerianLambda_mul (n : ℕ) (a b : ℚ) :
    eulerianLambda n a * eulerianLambda n b = eulerianLambda n (a * b) := by
  classical
  rw [eulerianLambda_eq_sum, eulerianLambda_eq_sum, eulerianLambda_eq_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul,
    eulerianElement_mul_fin]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl, ← mul_pow]
  · intro j hj hji
    rw [if_neg (Ne.symm hji), smul_zero]
  · simp

/-- Every actual rational convolution parameter has the original Eulerian eigenvalue on each supported piece. -/
theorem eulerianLambda_mul_eulerianElement (n i : ℕ) (hi : i ≤ n) (a : ℚ) :
    eulerianLambda n a * eulerianElement n i = a ^ i • eulerianElement n i := by
  classical
  let j₀ : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi⟩
  rw [eulerianLambda_eq_sum, Finset.sum_mul]
  simp only [smul_mul_assoc]
  simp_rw [(eulerianElement_projector_laws n).2]
  rw [Finset.sum_eq_single j₀]
  · simp [j₀]
  · intro j hj hne
    have hji : j.val ≠ i := fun h => hne (Fin.ext h)
    simp [hji]
  · simp

/-- Every nonzero actual rational convolution parameter gives an actual group-ring unit with its reciprocal
  operation. -/
def eulerianLambdaUnit (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (MonoidAlgebra ℚ (Perm (Fin n)))ˣ where
  val := eulerianLambda n a
  inv := eulerianLambda n a⁻¹
  val_inv := by rw [eulerianLambda_mul, mul_inv_cancel₀ ha, eulerianLambda_one]
  inv_val := by rw [eulerianLambda_mul, inv_mul_cancel₀ ha, eulerianLambda_one]

/-- The actual unit retains the original parameter operation as its forward value. -/
theorem eulerianLambdaUnit_val (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (eulerianLambdaUnit n a ha).val = eulerianLambda n a := rfl

/-- The actual unit retains the reciprocal parameter operation as its inverse value. -/
theorem eulerianLambdaUnit_inv (n : ℕ) (a : ℚ) (ha : a ≠ 0) :
    (eulerianLambdaUnit n a ha).inv = eulerianLambda n a⁻¹ := rfl

/-- The actual first-block group action used by the rational convolution family. -/
def eulerianBlockLeftAction (p q : ℕ) :
    MonoidAlgebra ℚ (Perm (Fin p)) →ₐ[ℚ] MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (blockLeftHom p q)

/-- The actual second-block group action used by the rational convolution family. -/
def eulerianBlockRightAction (p q : ℕ) :
    MonoidAlgebra ℚ (Perm (Fin q)) →ₐ[ℚ] MonoidAlgebra ℚ (Perm (Fin (p + q))) :=
  MonoidAlgebra.mapDomainAlgHom ℚ ℚ (blockRightHom p q)

/-- The original two-block evaluated element is the product of its original block actions. -/
theorem splitEulerianLambda_eq_blockActions (p q : ℕ) (a : ℚ) :
    splitEulerianLambda p q a = eulerianBlockLeftAction p q (eulerianLambda p a) *
      eulerianBlockRightAction p q (eulerianLambda q a) := rfl

/-- The actual two-block family has its original finite polynomial coefficient expansion. -/
theorem splitEulerianLambda_eq_eulerian_sum (p q : ℕ) (a : ℚ) :
    splitEulerianLambda p q a =
      ∑ z : Fin (p + 1) × Fin (q + 1), a ^ (z.1.val + z.2.val) •
        (eulerianBlockLeftAction p q (eulerianElement p z.1.val) *
          eulerianBlockRightAction p q (eulerianElement q z.2.val)) := by
  classical
  rw [splitEulerianLambda_eq_blockActions, eulerianLambda_eq_sum, eulerianLambda_eq_sum,
    map_sum, map_sum]
  simp_rw [map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← pow_add]
  rw [Fintype.sum_prod_type]

/-- The actual rational-parameter convolution family respects the original signed shuffle element. -/
theorem eulerianLambda_mul_signedShuffle_rat (p q : ℕ) (a : ℚ) :
    eulerianLambda (p + q) a * signedShuffleElement p q =
      signedShuffleElement p q * splitEulerianLambda p q a := by
  classical
  let left (z : Fin (p + q + 1)) := eulerianElement (p + q) z.val * signedShuffleElement p q
  let right (z : Fin (p + 1) × Fin (q + 1)) := signedShuffleElement p q *
    (eulerianBlockLeftAction p q (eulerianElement p z.1.val) *
      eulerianBlockRightAction p q (eulerianElement q z.2.val))
  have hleft (t : ℚ) : eulerianLambda (p + q) t * signedShuffleElement p q =
      Polynomial.finiteWeightedPowerCombination Fin.val left t := by
    rw [eulerianLambda_eq_sum, Finset.sum_mul]
    simp only [Polynomial.finiteWeightedPowerCombination, left, smul_mul_assoc]
  have hright (t : ℚ) : signedShuffleElement p q * splitEulerianLambda p q t =
      Polynomial.finiteWeightedPowerCombination (fun z => z.1.val + z.2.val) right t := by
    rw [splitEulerianLambda_eq_eulerian_sum, Finset.mul_sum]
    simp only [Polynomial.finiteWeightedPowerCombination, right, mul_smul_comm]
  rw [hleft, hright]
  apply Polynomial.finiteWeightedPowerCombination_eq_of_nat
  intro m
  rw [← hleft, ← hright]
  exact eulerianLambda_mul_signedShuffle p q m

end Equiv.Perm
