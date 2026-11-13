/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

private theorem coeff_succ_X_mul (G : PowerSeries ℚ) (m : ℕ) :
    PowerSeries.coeff (m + 1) (PowerSeries.X * G) = PowerSeries.coeff m G := by
  rw [PowerSeries.coeff_mul]
  refine (Finset.sum_eq_single (1, m) ?_ ?_).trans ?_
  · intro p hp hne
    have h1 : p.1 ≠ 1 := by
      intro hcon
      apply hne
      simp at hp
      exact Prod.ext hcon (by omega)
    simp [PowerSeries.coeff_X, h1]
  · intro hcon
    exfalso
    revert hcon
    simp [add_comm]
  · simp [PowerSeries.coeff_X]

private theorem coeff_bernoulli_sq (k : ℕ) :
    PowerSeries.coeff (k + 1) (bernoulliPowerSeries ℚ * bernoulliPowerSeries ℚ) =
      (∑ i ∈ Finset.range (k + 1 + 1), ((k + 1).choose i : ℚ) * bernoulli i
        * bernoulli (k + 1 - i)) / ((Nat.factorial (k + 1) : ℕ) : ℚ) := by
  have hne : ∀ j : ℕ, (((Nat.factorial j : ℕ)) : ℚ) ≠ 0 := fun j => by
    exact_mod_cast Nat.factorial_ne_zero j
  have hchoose : ∀ i : ℕ, i ≤ k + 1 →
      (((k + 1).choose i : ℕ) : ℚ) = (((Nat.factorial (k + 1) : ℕ)) : ℚ) /
        (((Nat.factorial i : ℕ) : ℚ) * (((Nat.factorial (k + 1 - i) : ℕ)) : ℚ)) := by
    intro i hi
    rw [Nat.choose_eq_factorial_div_factorial hi,
      Nat.cast_div (Nat.factorial_mul_factorial_dvd_factorial hi) (by
        exact_mod_cast Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)),
      Nat.cast_mul]
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div,
    Nat.succ_eq_add_one]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi2 : i ≤ k + 1 := by
    simp at hi
    omega
  simp only [bernoulliPowerSeries, PowerSeries.coeff_mk, Algebra.algebraMap_self,
    RingHom.id_apply]
  rw [hchoose i hi2]
  field_simp

/-- **Euler's convolution identity for Bernoulli numbers.** Let $B_j$ denote the $j$-th
Bernoulli number, with $B_1 = -1/2$. For every natural number $n \ge 1$,
$$\sum_{i=0}^{n} \binom{n}{i} B_i B_{n-i} = -n B_{n-1} - (n-1) B_n.$$

Proves `Wanted` entry `euler_bernoulli_convolution`.

Source: Ken Kamano, "Sums of Products of Bernoulli Numbers, Including
Poly-Bernoulli Numbers," Journal of Integer Sequences 13 (2010),
<https://cs.uwaterloo.ca/journals/JIS/VOL13/Kamano/kamano2.tex>.
Exact source span: lines 98–104; full-file SHA-256
`79c8704d7903524fdbe7553c7794f6062710b3f2c722eceb2715401659c869d6`;
span SHA-256 `c6021b742947f7d2dd79387b89f2f146c19cd8310add80520069b7eaf2103fb5`.
-/
theorem euler_bernoulli_convolution (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℚ) * bernoulli i * bernoulli (n - i) =
      -(n : ℚ) * bernoulli (n - 1) - ((n : ℚ) - 1) * bernoulli n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp only [Nat.succ_eq_add_one]
  have hBE := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have h2 : bernoulliPowerSeries ℚ ^ 2 + PowerSeries.X * bernoulliPowerSeries ℚ
      + PowerSeries.X * ⇑PowerSeries.derivative (bernoulliPowerSeries ℚ)
      = bernoulliPowerSeries ℚ := by
    have h1 : bernoulliPowerSeries ℚ * PowerSeries.exp ℚ
        + (PowerSeries.exp ℚ - 1) * ⇑PowerSeries.derivative (bernoulliPowerSeries ℚ) = 1 := by
      have h := congrArg (⇑PowerSeries.derivative : PowerSeries ℚ → PowerSeries ℚ) hBE
      rw [Derivation.leibniz] at h
      simp only [map_sub, PowerSeries.derivative_exp, PowerSeries.derivative_one, sub_zero,
        PowerSeries.derivative_X, smul_eq_mul] at h
      exact h
    have h1B := congrArg (bernoulliPowerSeries ℚ * ·) h1
    simp only [mul_add, mul_one] at h1B
    linear_combination h1B - (bernoulliPowerSeries ℚ
      + ⇑PowerSeries.derivative (bernoulliPowerSeries ℚ)) * hBE
  have hcoeff := congrArg (PowerSeries.coeff (m + 1)) h2
  simp only [map_add] at hcoeff
  rw [pow_two, coeff_bernoulli_sq m, coeff_succ_X_mul, coeff_succ_X_mul,
    PowerSeries.coeff_derivative] at hcoeff
  have hB0 : PowerSeries.coeff m (bernoulliPowerSeries ℚ)
      = bernoulli m / ((Nat.factorial m : ℕ) : ℚ) := by
    simp [bernoulliPowerSeries]
  have hB1 : PowerSeries.coeff (m + 1) (bernoulliPowerSeries ℚ)
      = bernoulli (m + 1) / ((Nat.factorial (m + 1) : ℕ) : ℚ) := by
    simp [bernoulliPowerSeries]
  rw [hB0, hB1] at hcoeff
  simp only [Nat.add_sub_cancel]
  have hF0 : (((Nat.factorial m : ℕ)) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hC : ((m : ℚ) + 1) ≠ 0 := by positivity
  have eF : (((Nat.factorial (m + 1) : ℕ)) : ℚ)
      = ((m : ℚ) + 1) * (((Nat.factorial m : ℕ)) : ℚ) := by
    rw [Nat.factorial_succ m, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  push_cast at hcoeff ⊢
  rw [eF] at hcoeff
  have hCF0 : ((m : ℚ) + 1) * (((Nat.factorial m : ℕ)) : ℚ) ≠ 0 :=
    mul_ne_zero hC hF0
  field_simp at hcoeff
  linear_combination hcoeff

end

end MetaMathlibExt
