/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Combinatorics.Perm.CyclicDescentDeletion
public import MathlibExt.Combinatorics.Perm.EulerianPolynomialCoefficients

/-!
# Actual cyclic averages of the convolution coefficient at two

For `L=n+1` original letters, the actual rotation fibers have `t` low
ordinary descents and `L-t` high ordinary descents. Head fixing gives
`t=descentNumber π+1` for a nonempty tail. The explicit descent-binomial
value at two therefore averages to twice the original tail coefficient.

All rotation and descent counts are proved from the original permutation
word. No averaged coefficient identity is provided by a caller. The
one-letter/empty-tail coefficient is handled by its actual polynomial.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- The actual coefficient average in every original rotation/head-fixing fiber. -/
theorem descentBinomial_rotation_average_two
    (n : ℕ) (r₀ : Fin (n + 1)) (π : Perm (Fin n)) :
    (∑ r : Fin (n + 1),
      (descentBinomialPolynomial (n + 1)
        (descentNumber ((finRotate (n + 1) ^ r₀.val * headFixingHom n π) *
          finRotate (n + 1) ^ r.val))).eval 2) =
      2 * (descentBinomialPolynomial n (descentNumber π)).eval 2 := by
  classical
  cases n with
  | zero =>
    have hr : r₀ = 0 := by
      apply Fin.ext
      have hrlt := r₀.isLt
      change r₀.val = 0
      omega
    have hπ : π = 1 := Subsingleton.elim _ _
    subst r₀
    subst π
    rw [Fin.sum_univ_succ]
    rw [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    simp only [Fin.val_zero, pow_zero, one_mul, map_one, mul_one]
    have hd₀ : descentNumber (1 : Perm (Fin 0)) = 0 :=
      (descentNumber_eq_zero_iff (1 : Perm (Fin 0))).mpr rfl
    have hd₁ : descentNumber (1 : Perm (Fin 1)) = 0 :=
      (descentNumber_eq_zero_iff (1 : Perm (Fin 1))).mpr rfl
    rw [hd₀, hd₁]
    simp [descentBinomialPolynomial]
  | succ n =>
    let σ : Perm (Fin (n + 2)) := finRotate (n + 2) ^ r₀.val * headFixingHom (n + 1) π
    have hcyc : cyclicDescentNumber σ = descentNumber π + 1 := by
      dsimp only [σ]
      rw [cyclicDescentNumber_rotate_values_pow,
        cyclicDescentNumber_headFixing (n + 1) π (Nat.zero_lt_succ _)]
    have hd : descentNumber π < n + 1 := descentNumber_lt π (Nat.zero_lt_succ _)
    change (∑ r : Fin (n + 2),
      (descentBinomialPolynomial (n + 2) (descentNumber (σ * finRotate (n + 2) ^ r.val))).eval 2) = _
    rw [sum_descentNumber_rotations σ
      (fun d => (descentBinomialPolynomial (n + 2) d).eval 2), hcyc, Nat.add_sub_cancel]
    rw [descentBinomialPolynomial_eval_two (n + 2) (descentNumber π) (by omega) (by omega),
      descentBinomialPolynomial_eval_two (n + 2) (descentNumber π + 1) (by omega) (by omega),
      descentBinomialPolynomial_eval_two (n + 1) (descentNumber π) (by omega) hd]
    by_cases h₀ : descentNumber π = 0
    · rw [h₀]
      simp only [zero_add, zero_ne_one, if_true, if_false, Nat.add_sub_cancel,
        one_nsmul, nsmul_eq_mul]
      push_cast
      ring
    · by_cases h₁ : descentNumber π = 1
      · rw [h₁]
        norm_num
      · have hplus₀ : descentNumber π + 1 ≠ 0 := by omega
        have hplus₁ : descentNumber π + 1 ≠ 1 := by omega
        simp only [h₀, h₁, hplus₀, hplus₁, if_false, nsmul_zero, zero_add, mul_zero]

/-- Actual inverse rotations have the same coefficient average as the original forward rotations. -/
theorem descentBinomial_rotation_average_two_inverse
    (n : ℕ) (r₀ : Fin (n + 1)) (π : Perm (Fin n)) :
    (∑ r : Fin (n + 1),
      (descentBinomialPolynomial (n + 1)
        (descentNumber ((finRotate (n + 1) ^ r₀.val * headFixingHom n π) *
          (finRotate (n + 1) ^ r.val)⁻¹))).eval 2) =
      2 * (descentBinomialPolynomial n (descentNumber π)).eval 2 := by
  classical
  simp_rw [rotationPower_inverse]
  have h := Fintype.sum_equiv (Equiv.neg (Fin (n + 1)))
    (fun r : Fin (n + 1) =>
      (descentBinomialPolynomial (n + 1)
        (descentNumber ((finRotate (n + 1) ^ r₀.val * headFixingHom n π) *
          finRotate (n + 1) ^ (-r).val))).eval 2)
    (fun r : Fin (n + 1) =>
      (descentBinomialPolynomial (n + 1)
        (descentNumber ((finRotate (n + 1) ^ r₀.val * headFixingHom n π) *
          finRotate (n + 1) ^ r.val))).eval 2)
    (fun _ => rfl)
  exact h.trans (descentBinomial_rotation_average_two n r₀ π)

end Equiv.Perm
