/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.Derivation.IteratePower
public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.RingTheory.Binomial

@[expose] public section

example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (r : R) (epsilon : A)
    (h : D epsilon = r • epsilon ^ 2) (n m : ℕ) :
    (D : A → A)^[n] (epsilon ^ m) =
      (r ^ n * (m.ascFactorial n : R)) • epsilon ^ (m + n) :=
  D.iterate_pow_of_apply_eq_smul_sq r epsilon h n m

private theorem source_iter_pos {A : Type*} [CommRing A] [Algebra ℚ A]
    (D : Derivation ℚ A A) {epsilon : A} (h : D epsilon = epsilon ^ 2) (b m : ℕ) :
    (m.factorial : ℚ) • (D : A → A)^[b] (epsilon ^ (m + 1)) =
      ((m + b).factorial : ℚ) • epsilon ^ (m + 1 + b) := by
  rw [D.iterate_pow_of_apply_eq_smul_sq 1 epsilon (by simpa using h)]
  simp only [one_pow, one_mul, smul_smul]
  congr 1
  exact_mod_cast Nat.factorial_mul_ascFactorial m b

private theorem source_iter_neg {A : Type*} [CommRing A] [Algebra ℚ A]
    (D : Derivation ℚ A A) {epsilon : A} (h : D epsilon = -epsilon ^ 2) (a m : ℕ) :
    (D : A → A)^[a] (epsilon ^ m) =
      ((a.factorial : ℚ) * (Ring.choose (-(m : ℤ)) a : ℤ)) • epsilon ^ (m + a) := by
  rw [D.iterate_pow_of_apply_eq_smul_sq (-1) epsilon (by simpa using h)]
  congr 1
  rcases m with _ | m
  · cases a <;> simp [Nat.zero_ascFactorial]
  · rw [Nat.ascFactorial_eq_factorial_mul_choose, Ring.choose_neg]
    have hu : ((m + 1 : ℕ) : ℤ) + (a : ℤ) - 1 = ((m + a : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hu, Ring.choose_natCast]
    have hz : (a : ℤ).negOnePow • ((m + a).choose a : ℤ) =
        (a : ℤ).negOnePow * ((m + a).choose a : ℤ) :=
      zsmul_eq_mul _ _
    rw [hz]
    push_cast
    rw [Int.coe_negOnePow_natCast]
    push_cast
    ring

-- The exact positive source formula follows from the generalized API.
example {A : Type*} [CommRing A] [Algebra ℚ A]
    (D : Derivation ℚ A A) {epsilon : A} (h : D epsilon = epsilon ^ 2) (b m : ℕ) :
    (m.factorial : ℚ) • (D : A → A)^[b] (epsilon ^ (m + 1)) =
      ((m + b).factorial : ℚ) • epsilon ^ (m + 1 + b) :=
  source_iter_pos D h b m

-- The exact negative source formula retains its generalized binomial coefficient.
example {A : Type*} [CommRing A] [Algebra ℚ A]
    (D : Derivation ℚ A A) {epsilon : A} (h : D epsilon = -epsilon ^ 2) (a m : ℕ) :
    (D : A → A)^[a] (epsilon ^ m) =
      ((a.factorial : ℚ) * (Ring.choose (-(m : ℤ)) a : ℤ)) • epsilon ^ (m + a) :=
  source_iter_neg D h a m

-- The zeroth iterate is the original power.
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (r : R) (epsilon : A) (_h : D epsilon = r • epsilon ^ 2)
    (m : ℕ) : (D : A → A)^[0] (epsilon ^ m) = epsilon ^ m := by
  simp

-- Every iterate of the zeroth power past order zero vanishes.
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (r : R) (epsilon : A) (h : D epsilon = r • epsilon ^ 2)
    (n : ℕ) : (D : A → A)^[n + 1] (epsilon ^ 0) = 0 := by
  rw [D.iterate_pow_of_apply_eq_smul_sq r epsilon h]
  simp [Nat.zero_ascFactorial]

-- A zero quadratic coefficient kills every positive iterate.
example {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (epsilon : A) (h : D epsilon = 0) (n m : ℕ) :
    (D : A → A)^[n + 1] (epsilon ^ m) = 0 := by
  rw [D.iterate_pow_of_apply_eq_smul_sq 0 epsilon (by simpa using h)]
  simp

private noncomputable def quadraticPolynomialDerivation {R : Type*} [CommRing R] :
    Derivation R (Polynomial R) (Polynomial R) :=
  (Polynomial.X : Polynomial R) ^ 2 •
    (Polynomial.derivative' : Derivation R (Polynomial R) (Polynomial R))

private theorem quadraticPolynomialDerivation_X {R : Type*} [CommRing R] :
    quadraticPolynomialDerivation (R := R) Polynomial.X = Polynomial.X ^ 2 := by
  simp [quadraticPolynomialDerivation]

-- The first three populated rational outputs have coefficients `1`, `2`, and `24`.
example : quadraticPolynomialDerivation (R := ℚ) Polynomial.X = Polynomial.X ^ 2 :=
  quadraticPolynomialDerivation_X

example :
    ((quadraticPolynomialDerivation (R := ℚ) : Polynomial ℚ → Polynomial ℚ)^[2])
        Polynomial.X = Polynomial.C 2 * Polynomial.X ^ 3 := by
  conv_lhs => rw [← pow_one Polynomial.X]
  rw [quadraticPolynomialDerivation.iterate_pow_of_apply_eq_smul_sq 1 Polynomial.X
    (by simpa using quadraticPolynomialDerivation_X (R := ℚ))]
  norm_num [Nat.ascFactorial_succ, Polynomial.smul_eq_C_mul]

example :
    ((quadraticPolynomialDerivation (R := ℚ) : Polynomial ℚ → Polynomial ℚ)^[3])
        (Polynomial.X ^ 2) = Polynomial.C 24 * Polynomial.X ^ 5 := by
  rw [quadraticPolynomialDerivation.iterate_pow_of_apply_eq_smul_sq 1 Polynomial.X
    (by simpa using quadraticPolynomialDerivation_X (R := ℚ))]
  norm_num [Nat.ascFactorial_succ, Polynomial.smul_eq_C_mul]

private noncomputable def negativeQuadraticPolynomialDerivation :
    Derivation ℚ (Polynomial ℚ) (Polynomial ℚ) :=
  -quadraticPolynomialDerivation

-- Negating the derivation negates its odd third iterate.
example :
    ((negativeQuadraticPolynomialDerivation : Polynomial ℚ → Polynomial ℚ)^[3])
        (Polynomial.X ^ 2) = -Polynomial.C 24 * Polynomial.X ^ 5 := by
  rw [negativeQuadraticPolynomialDerivation.iterate_pow_of_apply_eq_smul_sq
    (-1) Polynomial.X]
  · norm_num [Nat.ascFactorial_succ, Polynomial.smul_eq_C_mul]
  · simp [negativeQuadraticPolynomialDerivation, quadraticPolynomialDerivation_X]

-- In characteristic two the first image is nonzero, while the second iterate vanishes.
example :
    quadraticPolynomialDerivation (R := ZMod 2) Polynomial.X = Polynomial.X ^ 2 ∧
      (Polynomial.X : Polynomial (ZMod 2)) ^ 2 ≠ 0 := by
  refine ⟨quadraticPolynomialDerivation_X, ?_⟩
  intro h
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 2) h
  simp [Polynomial.coeff_X_pow] at hc

example :
    ((quadraticPolynomialDerivation (R := ZMod 2) :
      Polynomial (ZMod 2) → Polynomial (ZMod 2))^[2]) Polynomial.X = 0 := by
  conv_lhs => rw [← pow_one Polynomial.X]
  rw [quadraticPolynomialDerivation.iterate_pow_of_apply_eq_smul_sq 1 Polynomial.X
    (by simpa using quadraticPolynomialDerivation_X (R := ZMod 2))]
  norm_num [Nat.ascFactorial_succ, Polynomial.smul_eq_C_mul]
  rw [show (2 : ZMod 2) = 0 from CharP.cast_eq_zero (ZMod 2) 2]
  simp
