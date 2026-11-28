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
# Rotation sums of descent coefficients at two

For `N=n+1`, `ρ=finRotate N`, and `σ=ρ^r₀ H_n(π)`, the sum over all position rotations is `∑ r
: Fin N, P_(N,d(σρ^r))(2) = 2 P_(n,d(π))(2)`. Using inverse rotations gives the same value.

The sum has no division by `N`. A one-letter word has zero cyclic descents and contributes
`P_(1,0)(2)=2`, agreeing with the empty-tail value `2P_(0,0)(2)`.

Reference: Loday, *Cyclic Homology*, Section 4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, `r₀ : Fin N`, and `π ∈ S_n`. Put `σ = ρ^r₀.val *
headFixingHom n π` and `P_(r,d)(X)=(1/r!)∏_(j=0)^(r-1)(X+j-d)` in `ℚ[X]`. The unnormalized
rotation sum satisfies `∑ r : Fin N, P_(N,descentNumber(σ*ρ^r.val))(2) = 2 *
P_(n,descentNumber π)(2)`. This holds for every tail length `n`, including `n=0`. -/
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
      (descentBinomialPolynomial (n + 2)
        (descentNumber (σ * finRotate (n + 2) ^ r.val))).eval 2) = _
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

/-- Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, `r₀ : Fin N`, and `π ∈ S_n`. Put `σ = ρ^r₀.val *
headFixingHom n π` and `P_(r,d)(X)=(1/r!)∏_(j=0)^(r-1)(X+j-d)` in `ℚ[X]`. The
inverse-position-rotation sum satisfies `∑ r : Fin N, P_(N,descentNumber(σ*(ρ^r.val)⁻¹))(2) =
2 * P_(n,descentNumber π)(2)`, including the empty tail. -/
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
