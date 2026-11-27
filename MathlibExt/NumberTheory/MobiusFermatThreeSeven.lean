/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.MobiusFermat
import MathlibExt.NumberTheory.BangZsigmondy
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The Möbius–Fermat function on products of powers of three and seven

We compute the Dirichlet inverse of the Fermat unit function at `3 ^ m * 7 ^ n` as a signed
binomial sum and give the corresponding factorial formula.
-/

open ArithmeticFunction Finset PowerSeries

namespace MetaMathlibExt
namespace mobiusFermat_three_pow_mul_seven_pow

private def value (m n : ℕ) := 3 ^ m * 7 ^ n

private theorem value_add (a b c d : ℕ) :
    value (a + c) (b + d) = value a b * value c d := by
  simp only [value, pow_add]
  ac_rfl

private theorem value_dvd {a b m n : ℕ} : value a b ∣ value m n ↔ a ≤ m ∧ b ≤ n := by
  have h : Nat.Coprime 3 7 := by decide
  constructor
  · intro hd
    have h₃ := ((h.pow a n).dvd_mul_right).mp ((dvd_mul_right _ _).trans hd)
    have h₇ := ((h.symm.pow b m).dvd_mul_left).mp ((dvd_mul_left _ _).trans hd)
    exact ⟨(Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (3 : ℕ))).mp h₃,
      (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (7 : ℕ))).mp h₇⟩
  · rintro ⟨ha, hb⟩
    exact Nat.mul_dvd_mul (pow_dvd_pow _ ha) (pow_dvd_pow _ hb)

-- At every index above three except six, a primitive prime divisor excludes both 3 and 7.
private theorem unit_support {m n d : ℕ} (hd : d ∣ value m n) (hu : fermatUnitFunction d ≠ 0) :
    d ∈ ({1, 3, 7, 63} : Finset ℕ) := by
  change (if d ≠ 0 ∧ _ then (1 : ℤ) else 0) ≠ 0 at hu
  split at hu
  next h =>
    obtain ⟨hd0, he⟩ := h
    generalize Nat.log 2 (d + 1) = k at he
    by_cases hk : k ≤ 3
    · interval_cases k <;> norm_num at he <;> simp <;> omega
    by_cases h6 : k = 6
    · subst k
      norm_num at he
      simp
      omega
    have hexc : ¬ IsBangZsigmondyExceptional 2 1 k := by
      rintro (⟨_, _, rfl⟩ | ⟨rfl, _⟩) <;> omega
    obtain ⟨p, hp⟩ := bangZsigmondy_exists_primitivePrimeDivisor (by decide : 0 < 1)
      (by decide : 1 < 2) (by decide) (by omega : 2 ≤ k) hexc
    have he' : (2 : ℤ) ^ k - 1 ^ k = d := by
      have heZ : (2 : ℤ) ^ k = d + 1 := by exact_mod_cast he
      simp [heZ]
    have hpdiv := (Int.natCast_dvd_natCast.mp (he' ▸ hp.dvd)).trans hd
    rcases hp.prime.dvd_mul.mp hpdiv with h3 | h7
    · have hp3 := hp.prime.dvd_of_dvd_pow h3
      exact (hp.not_dvd_of_lt (by decide : 1 ≤ 2) (by omega)
        (by norm_num; exact_mod_cast hp3)).elim
    · have hp7 := hp.prime.dvd_of_dvd_pow h7
      exact (hp.not_dvd_of_lt (by decide : 1 ≤ 3) (by omega)
        (by norm_num; exact_mod_cast hp7)).elim
  next => contradiction

-- A factor with exponents (a,b) shifts the inverse by those exponents when it divides.
private def shift (μ : ArithmeticFunction ℤ) (a b m n : ℕ) : ℤ :=
  if a ≤ m ∧ b ≤ n then μ (value (m - a) (n - b)) else 0

private theorem shift_eq (μ : ArithmeticFunction ℤ) (a b m n : ℕ) :
    (if value a b ∣ value m n then μ (value m n / value a b) else 0) = shift μ a b m n := by
  simp only [value_dvd, shift]
  split
  next h =>
    have he := value_add (m - a) (n - b) a b
    rw [Nat.sub_add_cancel h.1, Nat.sub_add_cancel h.2] at he
    rw [he, Nat.mul_div_cancel _ (by unfold value; positivity)]
  next => rfl

private theorem convolution (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1)
    (m n : ℕ) :
    μ (value m n) + shift μ 1 0 m n + shift μ 0 1 m n + shift μ 2 1 m n =
      if m = 0 ∧ n = 0 then 1 else 0 := by
  let S : Finset ℕ := {1, 3, 7, 63}
  let l := value m n
  have hl : l ≠ 0 := by dsimp [l, value]; positivity
  have hunit (d : ℕ) (hd : d ∈ S) : fermatUnitFunction d = 1 := by
    simp only [S, mem_insert, mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> decide
  have h := DFunLike.congr_fun hμ l
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal'
    (fun a b => μ a * fermatUnitFunction b)] at h
  have hsum : ∑ d ∈ l.divisors, μ (l / d) * fermatUnitFunction d =
      ∑ d ∈ S, if d ∣ l then μ (l / d) else 0 := by
    calc
      _ = ∑ d ∈ l.divisors ∩ S, μ (l / d) := by
        rw [← filter_mem_eq_inter, sum_filter]
        apply sum_congr rfl
        intro d hd
        by_cases hs : d ∈ S
        · simp [hs, hunit d hs]
        · have hz : fermatUnitFunction d = 0 := by
            by_contra hn
            exact hs (unit_support (Nat.mem_divisors.mp hd).1 hn)
          simp [hs, hz]
      _ = _ := by simp [inter_comm l.divisors, ← filter_mem_eq_inter, sum_filter, hl]
  rw [hsum] at h
  simp only [S, sum_insert (by decide : 1 ∉ ({3, 7, 63} : Finset ℕ)),
    sum_insert (by decide : 3 ∉ ({7, 63} : Finset ℕ)),
    sum_insert (by decide : 7 ∉ ({63} : Finset ℕ)), sum_singleton, one_dvd, ite_true,
    Nat.div_one] at h
  change μ l + ((if value 1 0 ∣ l then μ (l / value 1 0) else 0) +
    ((if value 0 1 ∣ l then μ (l / value 0 1) else 0) +
      (if value 2 1 ∣ l then μ (l / value 2 1) else 0))) = _ at h
  simp only [l, shift_eq, ArithmeticFunction.one_apply] at h
  simpa [value, add_assoc, Nat.pow_eq_one] using h

-- Removing the alternating sign gives rows with generating functions
-- (1 + X²)^n / (1 - X)^(n+1).
private noncomputable def row (μ : ArithmeticFunction ℤ) (n : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun m => (-1) ^ (m + n) * μ (value m n)

private theorem row_zero (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1) :
    row μ 0 * (1 - X) = 1 := by
  ext m
  rw [mul_sub, mul_one, map_sub, ← pow_one (X : ℤ⟦X⟧), coeff_mul_X_pow', coeff_one]
  have h := convolution μ hμ m 0
  cases m with
  | zero => simpa [row, shift] using h
  | succ m =>
    simp [shift] at h
    simp [row, pow_succ]
    linear_combination -(-1 : ℤ) ^ m * h

private theorem row_succ (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1)
    (n : ℕ) : row μ (n + 1) * (1 - X) = row μ n * (1 + X ^ 2) := by
  ext m
  rw [mul_sub, mul_add, mul_one, mul_one, map_sub, map_add,
    ← pow_one (X : ℤ⟦X⟧), coeff_mul_X_pow', pow_one, coeff_mul_X_pow']
  have h := convolution μ hμ m (n + 1)
  match m with
  | 0 =>
    simp [shift] at h
    simp [row, pow_succ]
    linear_combination -(-1 : ℤ) ^ n * h
  | 1 =>
    simp [shift] at h
    simp [row, pow_add]
    linear_combination (-1 : ℤ) ^ n * h
  | m + 2 =>
    simp [shift] at h
    simp [row, pow_add]
    linear_combination -((-1 : ℤ) ^ m * (-1 : ℤ) ^ n) * h

private theorem row_eq (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1)
    (n : ℕ) : row μ n = (PowerSeries.mk 1) ^ (n + 1) * (X ^ 2 + 1) ^ n := by
  let G : ℤ⟦X⟧ := PowerSeries.mk 1
  have hG : (1 - X) * G = 1 := (mul_comm ..).trans (mk_one_mul_one_sub_eq_one ℤ)
  induction n with
  | zero =>
    simpa [mul_assoc, hG, G] using congrArg (· * G) (row_zero μ hμ)
  | succ n ih =>
    calc
      row μ (n + 1) = (row μ (n + 1) * (1 - X)) * G := by rw [mul_assoc, hG, mul_one]
      _ = (row μ n * (1 + X ^ 2)) * G := by rw [row_succ μ hμ]
      _ = _ := by rw [ih]; dsimp [G]; ring

private theorem row_coeff (μ : ArithmeticFunction ℤ) (hμ : μ * fermatUnitFunction = 1)
    (m n : ℕ) :
    coeff m (row μ n) = ∑ j ∈ range (min (m / 2) n + 1),
      ((n.choose j * (m + n - 2 * j).choose (m - 2 * j) : ℕ) : ℤ) := by
  rw [row_eq μ hμ, mk_one_pow_eq_mk_choose_add, add_pow, mul_sum, map_sum]
  simp only [one_pow, mul_one, ← pow_mul, ← mul_assoc, coeff_mul_natCast, coeff_mul_X_pow',
    coeff_mk]
  let S := (range (n + 1)).filter fun j => 2 * j ≤ m
  have hS : S = range (min (m / 2) n + 1) := by
    ext j
    simp only [S, mem_filter, mem_range]
    omega
  rw [← hS]
  unfold S
  rw [sum_filter]
  apply sum_congr rfl
  intro j hj
  split_ifs with hj'
  · rw [show m + n - 2 * j = n + (m - 2 * j) by omega, Nat.choose_symm_add]
    simp [mul_comm]
  · simp

end mobiusFermat_three_pow_mul_seven_pow

open mobiusFermat_three_pow_mul_seven_pow in
/-- **The Möbius–Fermat function at $3^m 7^n$.** Let $u_M$ be the Fermat unit function
and let $\mu_M$ be an integer-valued arithmetic function with $\mu_M * u_M = \varepsilon$, where
$*$ is Dirichlet convolution and $\varepsilon$ is its identity, with $\varepsilon(1) = 1$ and
$\varepsilon(l) = 0$ for $l \ne 1$; thus $\mu_M$ is the Dirichlet inverse of $u_M$, the
Möbius–Fermat function.
Then for all integers $m, n \ge 0$,
$$\mu_M(3^m 7^n) = (-1)^{m+n} \sum_{j=0}^{\min(\lfloor m/2 \rfloor, n)}
\binom{n}{j} \binom{m + n - 2j}{m - 2j},$$
and, as rational numbers,
$$\mu_M(3^m 7^n) = (-1)^{m+n} \sum_{j=0}^{\min(\lfloor m/2 \rfloor, n)}
\frac{(m + n - 2j)!}{(m - 2j)! \, (n - j)! \, j!}.$$

Source: J. L. Varona, *The Möbius and the von Mangoldt-type Functions of the Fermat Zeta
Function*, INTEGERS 26 (2026), Article A106, Proposition 7. -/
public theorem mobiusFermat_three_pow_mul_seven_pow (μ : ArithmeticFunction ℤ)
    (hμ : μ * fermatUnitFunction = 1) (m n : ℕ) :
    μ (3 ^ m * 7 ^ n) = (-1) ^ (m + n) *
        ∑ j ∈ Finset.range (min (m / 2) n + 1),
          ((n.choose j * (m + n - 2 * j).choose (m - 2 * j) : ℕ) : ℤ) ∧
      (μ (3 ^ m * 7 ^ n) : ℚ) = (-1) ^ (m + n) *
        ∑ j ∈ Finset.range (min (m / 2) n + 1),
          ((m + n - 2 * j).factorial : ℚ) /
            ((m - 2 * j).factorial * (n - j).factorial * j.factorial) := by
  have h := row_coeff μ hμ m n
  simp only [row, coeff_mk, value] at h
  have hsign : (-1 : ℤ) ^ (m + n) * (-1) ^ (m + n) = 1 := by rw [← mul_pow]; norm_num
  have hz := congrArg ((-1 : ℤ) ^ (m + n) * ·) h
  simp only [← mul_assoc, hsign, one_mul] at hz
  refine ⟨hz, ?_⟩
  rw [hz]
  push_cast
  congr 1
  apply sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by simp only [mem_range] at hj; omega
  have hjm : 2 * j ≤ m := by simp only [mem_range] at hj; omega
  rw [Nat.cast_choose ℚ hjn, Nat.cast_choose ℚ (by omega : m - 2 * j ≤ m + n - 2 * j),
    show m + n - 2 * j - (m - 2 * j) = n by omega]
  field_simp

end MetaMathlibExt
