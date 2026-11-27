/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.MinusculePolynomial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Log-concavity of type-A minuscule polynomial coefficients

We prove log-concavity directly from the coefficient formula, using the binomial coefficient
recurrence twice to compare consecutive odd-indexed terms of a binomial row.

## References

* Ming-Jian Ding and Jiang Zeng, *Some New Results on the Minuscule Polynomials of Type A*,
  Journal of Integer Sequences 28 (2025), Article 25.1.2, pp. 1–15, equation (1.1) and Corollary 7.
  The proof here uses (1.1) directly; the paper deduces Corollary 7 from real-rootedness.
* Petter Brändén, *Unimodality, Log-Concavity, Real-Rootedness and Beyond*, in *Handbook of
  Enumerative Combinatorics*, CRC Press, 2015, pp. 437–483, Lemma 7.1.1, supplies the
  real-rootedness implication used in the paper's proof.
-/

namespace MetaMathlibExt

open Polynomial

private theorem coeff_minusculePolynomialA (n k : ℕ) :
    (minusculePolynomialA n).coeff k =
      if k ∈ Finset.Icc 1 (n - 1) then
        (k : ℚ) * ((n : ℚ) - k) * (2 * n + 2).choose (2 * k + 1) / (4 * n + 2)
      else 0 := by
  simp only [minusculePolynomialA, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq]

-- Apply the adjacent binomial recurrence twice, keeping it in cross-multiplied form.
private theorem choose_add_two_mul (m j : ℕ) (hj : j + 2 ≤ m) :
    (m.choose (j + 2) : ℚ) * (((j : ℚ) + 1) * (j + 2)) =
      (m.choose j : ℚ) * (((m : ℚ) - j) * (m - j - 1)) := by
  have step (i : ℕ) (hi : i ≤ m) :
      (m.choose (i + 1) : ℚ) * ((i : ℚ) + 1) =
        (m.choose i : ℚ) * ((m : ℚ) - i) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) (Nat.choose_succ_right_eq m i)
    push_cast [Nat.cast_sub hi] at h
    exact h
  have h₀ := step j (by omega)
  have h₁ := step (j + 1) (by omega)
  push_cast at h₁
  linear_combination ((j : ℚ) + 1) * h₁ + ((m : ℚ) - j - 1) * h₀

private theorem choose_add_two_logConcave (m j : ℕ) (hj : j + 4 ≤ m) :
    (m.choose j : ℚ) * m.choose (j + 4) ≤ (m.choose (j + 2) : ℚ) ^ 2 := by
  let b (i : ℕ) : ℚ := m.choose i
  let loDenom : ℚ := ((j : ℚ) + 1) * (j + 2)
  let hiDenom : ℚ := ((j : ℚ) + 3) * (j + 4)
  let loNum : ℚ := ((m : ℚ) - j) * (m - j - 1)
  let hiNum : ℚ := ((m : ℚ) - j - 2) * (m - j - 3)
  have hlo : b (j + 2) * loDenom = b j * loNum := choose_add_two_mul m j (by omega)
  have hhi : b (j + 4) * hiDenom = b (j + 2) * hiNum := by
    have h := choose_add_two_mul m (j + 2) hj
    push_cast at h
    dsimp [b, hiDenom, hiNum]
    linear_combination h
  have hbound : (j : ℚ) + 4 ≤ m := by exact_mod_cast hj
  have hden : loDenom ≤ hiDenom := by
    dsimp [loDenom, hiDenom]
    gcongr <;> norm_num
  have hnum₀ : 0 ≤ (m : ℚ) - j - 2 := by linarith
  have hnum₁ : 0 ≤ (m : ℚ) - j - 3 := by linarith
  have hnum : hiNum ≤ loNum := by
    dsimp [hiNum, loNum]
    exact mul_le_mul (by linarith) (by linarith) hnum₁ (by linarith)
  have hpos : 0 < loNum * hiDenom := by
    have h₀ : 0 < (m : ℚ) - j := by linarith
    have h₁ : 0 < (m : ℚ) - j - 1 := by linarith
    dsimp [loNum, hiDenom]
    positivity
  change b j * b (j + 4) ≤ b (j + 2) ^ 2
  apply le_of_mul_le_mul_right _ hpos
  calc
    _ = (b j * loNum) * (b (j + 4) * hiDenom) := by ring
    _ = (b (j + 2) * loDenom) * (b (j + 2) * hiNum) := by rw [← hlo, hhi]
    _ = b (j + 2) ^ 2 * (loDenom * hiNum) := by ring
    _ ≤ b (j + 2) ^ 2 * (hiDenom * loNum) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hden hnum (mul_nonneg hnum₀ hnum₁) (by dsimp [hiDenom]; positivity))
        (sq_nonneg _)
    _ = _ := by ring

/-- **Log-concavity of the coefficients of the minuscule polynomials.** Let $N_{n,k}$ be the
coefficient of $x^k$ in the type-A minuscule polynomial $N_n(x)$. For all natural numbers $n$
and $k$, $N_{n,k-1} N_{n,k+1} \le N_{n,k}^2$, where for $k = 0$ the index $k - 1$ is read as $0$.

The cases outside $n \ge 1$, $1 \le k \le n - 1$ hold because the coefficients involved vanish.

Source: Ding and Zeng, *Some New Results on the Minuscule Polynomials of Type A*, Journal of
Integer Sequences 28 (2025), Article 25.1.2, Corollary 7. -/
public theorem minusculePolynomialA_coeff_logConcave (n k : ℕ) :
    (minusculePolynomialA n).coeff (k - 1) * (minusculePolynomialA n).coeff (k + 1) ≤
      (minusculePolynomialA n).coeff k ^ 2 := by
  by_cases hlow : k ≤ 1
  · rw [coeff_minusculePolynomialA n (k - 1),
      ite_eq_right (by simp only [Finset.mem_Icc]; omega), zero_mul]
    exact sq_nonneg _
  by_cases hhigh : n ≤ k + 1
  · rw [coeff_minusculePolynomialA n (k + 1),
      ite_eq_right (by simp only [Finset.mem_Icc]; omega), mul_zero]
    exact sq_nonneg _
  let w (i : ℕ) : ℚ := (i : ℚ) * ((n : ℚ) - i)
  let b (i : ℕ) : ℚ := (2 * n + 2).choose (2 * i + 1)
  let c : ℚ := (4 * (n : ℚ) + 2)⁻¹
  have hcoeff (i : ℕ) (hi : i ∈ Finset.Icc 1 (n - 1)) :
      (minusculePolynomialA n).coeff i = (w i * b i) * c := by
    simp only [coeff_minusculePolynomialA, ite_eq_left hi, div_eq_mul_inv, w, b, c]
  have hindex (i : ℕ) (hi₁ : 1 ≤ i) (hi₂ : i < n) : i ∈ Finset.Icc 1 (n - 1) :=
    Finset.mem_Icc.mpr ⟨hi₁, by omega⟩
  rw [hcoeff (k - 1) (hindex _ (by omega) (by omega)),
    hcoeff (k + 1) (hindex _ (by omega) (by omega)), hcoeff k (hindex _ (by omega) (by omega))]
  have hbin : b (k - 1) * b (k + 1) ≤ b k ^ 2 := by
    have e₁ : 2 * (k - 1) + 1 + 2 = 2 * k + 1 := by omega
    have e₂ : 2 * (k - 1) + 1 + 4 = 2 * (k + 1) + 1 := by omega
    simpa only [b, e₁, e₂] using
      choose_add_two_logConcave (2 * n + 2) (2 * (k - 1) + 1) (by omega)
  have hk : (↑(k - 1 : ℕ) : ℚ) * ↑(k + 1 : ℕ) ≤ (k : ℚ) ^ 2 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    nlinarith
  have hn : ((n : ℚ) - ↑(k - 1 : ℕ)) * ((n : ℚ) - ↑(k + 1 : ℕ)) ≤ ((n : ℚ) - k) ^ 2 := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
    nlinarith
  have hw : w (k - 1) * w (k + 1) ≤ w k ^ 2 := by
    have hsub (i : ℕ) (hi : i ≤ n) : 0 ≤ (n : ℚ) - i := sub_nonneg.mpr (by exact_mod_cast hi)
    calc
      _ = ((↑(k - 1 : ℕ) : ℚ) * ↑(k + 1 : ℕ)) *
          (((n : ℚ) - ↑(k - 1 : ℕ)) * ((n : ℚ) - ↑(k + 1 : ℕ))) := by dsimp [w]; ring
      _ ≤ (k : ℚ) ^ 2 * ((n : ℚ) - k) ^ 2 :=
        mul_le_mul hk hn (mul_nonneg (hsub _ (by omega)) (hsub _ (by omega))) (sq_nonneg _)
      _ = _ := by dsimp [w]; ring
  calc
    _ = (w (k - 1) * w (k + 1) * (b (k - 1) * b (k + 1))) * c ^ 2 := by ring
    _ ≤ (w k ^ 2 * b k ^ 2) * c ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hw hbin (by dsimp [b]; positivity) (sq_nonneg _)) (sq_nonneg _)
    _ = _ := by ring

end MetaMathlibExt
