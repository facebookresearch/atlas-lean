/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.TrinomialCoefficient
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private lemma base_reflect : Polynomial.reflect 2 (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) = 1 + Polynomial.X + Polynomial.X ^ 2 := by
  have h1 : Polynomial.reflect 2 (1 : Polynomial ℚ) = Polynomial.X ^ 2 := Polynomial.reflect_one 2
  have hX : Polynomial.reflect 2 (Polynomial.X : Polynomial ℚ) = Polynomial.X := by
    have h : (Polynomial.X : Polynomial ℚ) = (Polynomial.X : Polynomial ℚ) ^ 1 := by simp
    rw [h, Polynomial.reflect_monomial]
    simp
  have hX2 : Polynomial.reflect 2 ((Polynomial.X : Polynomial ℚ) ^ 2) = 1 := by
    rw [Polynomial.reflect_monomial]
    simp
  have hadd : Polynomial.reflect 2 ((1 : Polynomial ℚ) + Polynomial.X + Polynomial.X ^ 2)
      = Polynomial.reflect 2 (1 : Polynomial ℚ) + Polynomial.reflect 2 (Polynomial.X : Polynomial ℚ) + Polynomial.reflect 2 ((Polynomial.X : Polynomial ℚ) ^ 2) := by
    rw [Polynomial.reflect_add, Polynomial.reflect_add]
  rw [hadd, h1, hX, hX2]
  ring

private lemma base_natDegree : ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ)).natDegree ≤ 2 := by
  compute_degree

private lemma pow_reflect (n : ℕ) :
    Polynomial.reflect (2 * n) ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n) = (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n).natDegree ≤ 2 * n := by
      calc ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n).natDegree
          ≤ n * ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ).natDegree) := Polynomial.natDegree_pow_le
        _ ≤ n * 2 := by
            apply Nat.mul_le_mul_left
            exact base_natDegree
        _ = 2 * n := by ring
    have h2 : (2 : ℕ) * (n + 1) = 2 * n + 2 := by ring
    rw [h2, pow_succ]
    rw [Polynomial.reflect_mul _ _ hpow base_natDegree]
    rw [ih, base_reflect]

private lemma symm_succ (n : ℕ) :
    (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)).coeff (n+2))
      = (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)).coeff n) := by
  have h := pow_reflect (n+1)
  have h2 : ((Polynomial.reflect (2*(n+1)) ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1))).coeff (n+2))
      = (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)).coeff (n+2)) := by rw [h]
  rw [Polynomial.coeff_reflect] at h2
  have hrev : (Polynomial.revAt (2*(n+1))) (n+2) = n := by
    have hle : n + 2 ≤ 2 * (n+1) := by omega
    have heq : ((Polynomial.revAt (2*(n+1))) (n+2) : ℕ)
        = (if n+2 ≤ 2*(n+1) then 2*(n+1)-(n+2) else n+2) := rfl
    simp only [hle, ↓reduceIte] at heq
    omega
  rw [hrev] at h2
  exact h2.symm

private lemma symm_general (n : ℕ) (h1 : 1 ≤ n) :
    (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n).coeff (n+1))
      = (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n).coeff (n-1)) := by
  have h := pow_reflect n
  have h2 : ((Polynomial.reflect (2*n) ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n)).coeff (n+1))
      = (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n).coeff (n+1)) := by rw [h]
  rw [Polynomial.coeff_reflect] at h2
  have hrev : (Polynomial.revAt (2*n)) (n+1) = n-1 := by
    have hle : n + 1 ≤ 2 * n := by omega
    have heq : ((Polynomial.revAt (2*n)) (n+1) : ℕ)
        = (if n+1 ≤ 2*n then 2*n-(n+1) else n+1) := rfl
    simp only [hle, ↓reduceIte] at heq
    omega
  rw [hrev] at h2
  exact h2.symm

private lemma base_deriv : Polynomial.derivative (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) = 1 + Polynomial.C 2 * Polynomial.X := by
  simp only [Polynomial.derivative_add, Polynomial.derivative_one, Polynomial.derivative_X, Polynomial.derivative_X_pow]
  simp

private lemma aux_coeff (p : Polynomial ℚ) (m : ℕ) :
    ((p * (1 + Polynomial.C 2 * Polynomial.X)).coeff (m+1)) = p.coeff (m+1) + 2 * p.coeff m := by
  have hexpand : p * (1 + Polynomial.C 2 * Polynomial.X) = p + Polynomial.C 2 * (p * Polynomial.X) := by ring
  rw [hexpand, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X]

private lemma deriv1 (n : ℕ) :
    ((((n+2 : ℕ)) : ℚ)) * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)).coeff (n+2)))
      = (((n+1 : ℕ) : ℚ)) * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n).coeff (n+1))
        + 2 * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n).coeff n))) := by
  have hderiv : Polynomial.derivative (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)))
      = Polynomial.C (((n+1 : ℕ) : ℚ)) * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n) * (1 + Polynomial.C 2 * Polynomial.X))) := by
    rw [Polynomial.derivative_pow, base_deriv]
    have hsub : n + 1 - 1 = n := by omega
    rw [hsub]
    ring
  have hcoeff := congrArg (fun p : Polynomial ℚ => p.coeff (n+1)) hderiv
  simp only [Polynomial.coeff_derivative] at hcoeff
  rw [Polynomial.coeff_C_mul, aux_coeff] at hcoeff
  have hidx : n + 1 + 1 = n + 2 := by omega
  rw [hidx] at hcoeff
  push_cast at hcoeff ⊢
  linear_combination hcoeff

private lemma deriv2 (t : ℕ) :
    ((((t+2 : ℕ)) : ℚ)) * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (t+2)).coeff (t+2)))
      = (((t+2 : ℕ) : ℚ)) * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (t+1)).coeff (t+1))
        + 2 * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (t+1)).coeff t))) := by
  have hderiv : Polynomial.derivative (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (t+2)))
      = Polynomial.C ((((t+2 : ℕ) : ℚ))) * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (t+1)) * (1 + Polynomial.C 2 * Polynomial.X))) := by
    rw [Polynomial.derivative_pow, base_deriv]
    have hsub : t + 2 - 1 = t + 1 := by omega
    rw [hsub]
    ring
  have hcoeff := congrArg (fun p : Polynomial ℚ => p.coeff (t+1)) hderiv
  simp only [Polynomial.coeff_derivative] at hcoeff
  rw [Polynomial.coeff_C_mul, aux_coeff] at hcoeff
  have hidx : t + 1 + 1 = t + 2 := by omega
  rw [hidx] at hcoeff
  push_cast at hcoeff ⊢
  linear_combination hcoeff

private lemma mul_succ (n : ℕ) :
    (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+2)).coeff (n+2))
      = (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)).coeff (n+2))
        + (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)).coeff (n+1))
        + (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)).coeff n) := by
  have hpow : (1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+2)
      = ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)) * (1 + Polynomial.X + Polynomial.X ^ 2) := by
    rw [pow_succ]
  rw [hpow]
  have hexpand : (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)) * (1 + Polynomial.X + Polynomial.X ^ 2))
      = ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1))
        + ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)) * Polynomial.X
        + ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)) * Polynomial.X ^ 2 := by ring
  rw [hexpand, Polynomial.coeff_add, Polynomial.coeff_add]
  congr 1
  congr 1
  · have h1 : ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)) * Polynomial.X).coeff (n+2))
        = ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1))).coeff (n+1)) := by
      have : n + 2 = (n+1) + 1 := by omega
      rw [this]
      exact Polynomial.coeff_mul_X _ _
    exact h1
  · have h2 : ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1)) * Polynomial.X ^ 2).coeff (n+2))
        = ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1))).coeff n) := by
      have h := Polynomial.coeff_mul_X_pow (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (n+1))) 2 n
      exact h
    exact h2

private lemma coeff_transfer (n k : ℕ) :
    ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n).coeff k)) = (((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ n).coeff k) : ℕ) : ℚ) := by
  have hmap : Polynomial.map (Nat.castRingHom ℚ) (((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ n))
      = ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ n) := by
    rw [Polynomial.map_pow]
    congr 1
    simp [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X]
  have hcoeff := congrArg (fun p : Polynomial ℚ => p.coeff k) hmap
  simp only [Polynomial.coeff_map] at hcoeff
  simpa using hcoeff.symm

private lemma tri_zero : trinomialCoefficient 0 0 = 1 := by
  simp [trinomialCoefficient]

private lemma tri_one_one : trinomialCoefficient 1 1 = 1 := by
  unfold trinomialCoefficient
  simp [pow_one, Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]

private lemma tri_two_two : trinomialCoefficient 2 2 = 3 := by
  unfold trinomialCoefficient
  have h : ((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℕ) ^ 2)
      = 1 + 2 * Polynomial.X + 3 * Polynomial.X ^ 2 + 2 * Polynomial.X ^ 3 + Polynomial.X ^ 4 := by ring
  rw [h]
  simp [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_X, Polynomial.coeff_X_pow]

/--
**Three-term recurrence for central trinomial coefficients.** For a natural number $m$, let
$T_m$ be the central trinomial coefficient, the coefficient of $x^m$ in $(1 + x + x^2)^m$.
For every natural number $n$ the following holds, where for $n = 0$ the index $n - 1$ is read
as $0$ (the last term then vanishes, since $3n = 0$):
$$(n + 1)\,T_{n+1} = (2n + 1)\,T_n + 3n\,T_{n-1}.$$

Proves `Wanted` entry `centralTrinomialCoeff_three_term_recurrence`.

Source: P. Blasiak, G. Dattoli, A. Horzela, K. A. Penson, and K. Zhukovsky,
"Motzkin Numbers, Central Trinomial Coefficients and Hybrid Polynomials,"
Journal of Integer Sequences 11 (2008), Article 08.1.1,
Corollary containing Equation (24), lines 364–369,
<https://cs.uwaterloo.ca/journals/JIS/VOL11/Penson/penson131.tex>.
-/
theorem centralTrinomialCoeff_three_term_recurrence (n : ℕ) :
    (n + 1) * trinomialCoefficient (n + 1) (n + 1) =
      (2 * n + 1) * trinomialCoefficient n n +
        3 * n * trinomialCoefficient (n - 1) (n - 1) := by
  by_cases h : n < 2
  · interval_cases n
    · simp [tri_zero, tri_one_one]
    · simp [tri_one_one, tri_two_two, tri_zero]
  · have hle : 2 ≤ n := by omega
    obtain ⟨t, rfl⟩ : ∃ t, n = t + 2 := ⟨n - 2, by omega⟩
    have hsub : (t + 2) - 1 = t + 1 := by omega
    rw [hsub]
    have hE1 := mul_succ (t + 1)
    have hE2 := deriv1 (t + 1)
    have hE3 := deriv2 t
    have hE4 := symm_succ (t + 1)
    have hE5 := symm_general (t + 1) (by omega)
    have e1 : t + 1 + 2 = t + 3 := by omega
    have e2 : t + 1 + 1 = t + 2 := by omega
    have e3 : t + 1 - 1 = t := by omega
    rw [e1, e2] at hE1 hE2 hE4
    rw [e2, e3] at hE5
    have hsum : ((((2 * (t + 2) + 1 : ℕ)) : ℚ)) = ((((t + 3 : ℕ)) : ℚ)) + ((((t + 2 : ℕ)) : ℚ)) := by
      push_cast
      ring
    have hQ : ((((t + 3 : ℕ)) : ℚ)) * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (t + 3)).coeff (t + 3)))
        = ((((2 * (t + 2) + 1 : ℕ)) : ℚ)) * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (t + 2)).coeff (t + 2)))
          + 3 * ((((t + 2 : ℕ)) : ℚ)) * ((((1 + Polynomial.X + Polynomial.X ^ 2 : Polynomial ℚ) ^ (t + 1)).coeff (t + 1))) := by
      rw [hsum]
      linear_combination ((((t + 3 : ℕ)) : ℚ)) * hE1 + 2 * hE2 - hE3 - ((((t + 3 : ℕ)) : ℚ)) * hE4 + 2 * ((((t + 2 : ℕ)) : ℚ)) * hE5
    have hT3 := coeff_transfer (t + 3) (t + 3)
    have hT2 := coeff_transfer (t + 2) (t + 2)
    have hT1 := coeff_transfer (t + 1) (t + 1)
    have e6 : t + 2 + 1 = t + 3 := by omega
    have hcast : ((((t + 2 + 1) * trinomialCoefficient (t + 2 + 1) (t + 2 + 1) : ℕ)) : ℚ)
        = ((((2 * (t + 2) + 1) * trinomialCoefficient (t + 2) (t + 2) + 3 * (t + 2) * trinomialCoefficient (t + 1) (t + 1) : ℕ)) : ℚ) := by
      rw [e6]
      simp only [trinomialCoefficient, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
      push_cast at hQ ⊢
      rw [← hT3, ← hT2, ← hT1] at ⊢
      linear_combination hQ
    have e7 : t + 2 + 1 = (t + 2) + 1 := by omega
    have goal_eq : (t + 2 + 1) * trinomialCoefficient (t + 2 + 1) (t + 2 + 1)
        = (2 * (t + 2) + 1) * trinomialCoefficient (t + 2) (t + 2) + 3 * (t + 2) * trinomialCoefficient (t + 1) (t + 1) := by
      exact_mod_cast hcast
    simpa [e7] using goal_eq

end MetaMathlibExt
