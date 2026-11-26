/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.FinCases
import MathlibExt.NumberTheory.PadicValuationMinTwice
import MathlibExt.NumberTheory.PQDiophantineTuples

/-!
# The Szalay–Ziegler system (4)

The six prescribed factorizations in distinct odd primes have no solution with
`0 < a < b < c < d`.
-/

namespace MetaMathlibExt
namespace not_exists_sDiophantine_system_four

/-- If two products with a common factor are both `-1` modulo `m`, their other
factors are congruent modulo `m`. -/
private theorem factors_modEq {m x y z : ℕ} (hy : m ∣ y * x + 1) (hz : m ∣ z * x + 1) :
    y ≡ z [MOD m] := by
  have hcop : m.Coprime x := Nat.Coprime.of_dvd_left hy (by simp)
  exact Nat.ModEq.cancel_right_of_coprime hcop <|
    Nat.ModEq.add_right_cancel' 1 (hy.modEq_zero_nat.trans hz.zero_modEq_nat)

/-- If the first and third exponents differ, their minimum is below the last exponent,
and the overall minimum occurs twice, the second exponent equals the smaller of the two. -/
private theorem second_eq_min {x u v y : ℕ}
    (h : ∃ i j : Fin 4, i ≠ j ∧ (![x, u, v, y] : Fin 4 → ℕ) i = ![x, u, v, y] j ∧
      ∀ k, ![x, u, v, y] i ≤ ![x, u, v, y] k)
    (hne : x ≠ v) (hy : min x v < y) : u = min x v := by
  obtain ⟨i, j, hij, he, hmin⟩ := h
  have hx := hmin 0
  have hv := hmin 2
  fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val] <;> omega

end not_exists_sDiophantine_system_four

open not_exists_sDiophantine_system_four

set_option linter.unusedVariables false in
/-- **The Szalay–Ziegler system (4) has no solutions.** Let $p \ne q$ be odd primes and let
$a, b, c, d$ be integers with $0 < a < b < c < d$. Then there are no natural numbers
$\beta_1, \alpha_4, \beta_4, \alpha_2, \alpha_5, \alpha_3, \beta_3, \beta_6$ with
$ab + 1 = q^{\beta_1}$, $bc + 1 = p^{\alpha_4} q^{\beta_4}$, $ac + 1 = p^{\alpha_2}$,
$bd + 1 = p^{\alpha_5}$, $ad + 1 = p^{\alpha_3} q^{\beta_3}$ and $cd + 1 = q^{\beta_6}$.

Any solution would make $\{a, b, c, d\}$ a $\{p, q\}$-Diophantine quadruple.

Source: Volker Ziegler, *On the Existence of `{p, q}`-Diophantine Quadruples and Quintuples*,
INTEGERS 25 (2025), Article A92, Lemma 4, System (4), quoting Szalay and Ziegler, INTEGERS 13
(2013), Section 4 (`integers-2025-A92-lem-4`). -/
public theorem not_exists_sDiophantine_system_four {p q a b c d : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q) (ha : 0 < a) (hab : a < b)
    (hbc : b < c) (hcd : c < d) :
    ¬∃ β₁ α₄ β₄ α₂ α₅ α₃ β₃ β₆ : ℕ, a * b + 1 = q ^ β₁ ∧ b * c + 1 = p ^ α₄ * q ^ β₄ ∧
      a * c + 1 = p ^ α₂ ∧ b * d + 1 = p ^ α₅ ∧ a * d + 1 = p ^ α₃ * q ^ β₃ ∧
      c * d + 1 = q ^ β₆ := by
  rintro ⟨β₁, α₄, β₄, α₂, α₅, α₃, β₃, β₆, h₁, h₄, h₂, h₅, h₃, h₆⟩
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hα₂₅ : α₂ < α₅ := by
    apply (pow_lt_pow_iff_right₀ hp.one_lt).mp
    rw [← h₂, ← h₅]
    gcongr
  have hβ₁₆ : β₁ < β₆ := by
    apply (pow_lt_pow_iff_right₀ hq.one_lt).mp
    rw [← h₁, ← h₆]
    gcongr <;> omega
  -- Otherwise ac + 1 divides bc + 1, contrary to the ordering of a, b, c.
  have hα₄₂ : α₄ < α₂ := by
    by_contra! hle
    apply not_mul_add_one_dvd_mul_add_one ha hab hbc
    rw [h₂, h₄]
    exact dvd_mul_of_dvd_left (pow_dvd_pow p hle) _
  have hα₃₄ : α₃ = α₄ := by
    have hm := (padicValNat_two_smallest_eq hp a b c d).1
    simp only [Matrix.cons_val, h₂, h₃, h₄, h₅, Nat.padicValNat_def,
      Nat.multiplicity_prime_pow, multiplicity_mul_pow_left _ _ hpq] at hm
    simpa only [min_eq_right hα₄₂.le] using
      second_eq_min hm hα₄₂.ne' (lt_of_le_of_lt (min_le_left ..) hα₂₅)
  subst α₃
  let P := p ^ α₄
  have hPac : P ∣ a * c + 1 := h₂ ▸ pow_dvd_pow p hα₄₂.le
  have hPbc : P ∣ b * c + 1 := h₄ ▸ dvd_mul_right _ _
  have habP := factors_modEq hPac hPbc
  have hPb : P < b := by
    have := Nat.le_of_dvd (by omega : 0 < b - a) habP.dvd'
    omega
  -- The cofactor of P in bc + 1 exceeds c.
  have hcq : c < q ^ β₄ := by
    by_contra! hle
    exact (Nat.mul_le_mul hPb.le hle).not_gt (h₄ ▸ Nat.lt_succ_self _)
  have hQbc : q ^ β₄ ∣ b * c + 1 := h₄ ▸ dvd_mul_left _ _
  have hβ₁₄ : β₁ < β₄ := by
    by_contra! hle
    have hQab : q ^ β₄ ∣ a * b + 1 := h₁ ▸ pow_dvd_pow q hle
    have hQcb : q ^ β₄ ∣ c * b + 1 := by rwa [mul_comm c]
    have := Nat.le_of_dvd (by omega : 0 < c - a) (factors_modEq hQab hQcb).dvd'
    omega
  have hβ₃₁ : β₃ = β₁ := by
    have hm := (padicValNat_two_smallest_eq hq a b c d).2.2
    simp only [Matrix.cons_val, h₁, h₃, h₄, h₆, Nat.padicValNat_def,
      Nat.multiplicity_prime_pow, multiplicity_mul_pow_right _ _ hpq.symm] at hm
    simpa only [min_eq_left hβ₁₄.le] using
      second_eq_min hm hβ₁₄.ne (lt_of_le_of_lt (min_le_left ..) hβ₁₆)
  subst β₃
  let Q := q ^ β₁
  have hQ₄ : Q ∣ q ^ β₄ := pow_dvd_pow q hβ₁₄.le
  have hβ₄₆ : β₄ < β₆ := by
    apply (pow_lt_pow_iff_right₀ hq.one_lt).mp
    rw [← h₆]
    calc
      q ^ β₄ ≤ b * c + 1 := Nat.le_of_dvd (Nat.succ_pos _) hQbc
      _ < d * c + 1 := by gcongr <;> omega
      _ = c * d + 1 := by rw [mul_comm d]
  have hQdc : q ^ β₄ ∣ d * c + 1 := by
    rw [mul_comm d, h₆]
    exact pow_dvd_pow q hβ₄₆.le
  have hdvd := (factors_modEq hQbc hQdc).dvd'
  -- Write c - a = Qr and d - b = Qs. Since c < q^β₄ ≤ d - b, we get r < s.
  have hQab : Q ∣ a * b + 1 := h₁ ▸ dvd_refl _
  have hQcb : Q ∣ c * b + 1 := by
    rw [mul_comm c]
    exact hQ₄.trans hQbc
  obtain ⟨r, hr⟩ := (factors_modEq hQab hQcb).dvd'
  obtain ⟨s, hs⟩ := hQ₄.trans hdvd
  have hrs : r < s := by
    apply Nat.lt_of_mul_lt_mul_left (a := Q)
    have := Nat.le_of_dvd (by omega : 0 < d - b) hdvd
    omega
  have hsP : s < P := by
    apply Nat.lt_of_mul_lt_mul_left (a := Q)
    have := Nat.le_mul_of_pos_left d ha
    change a * d + 1 = P * Q at h₃
    rw [mul_comm P] at h₃
    omega
  -- Both pairs (a,b) and (c,d) are congruent modulo P, so r and s are too.
  have hPca : P ∣ c * a + 1 := by rwa [mul_comm c]
  have hPda : P ∣ d * a + 1 := by
    rw [mul_comm d, h₃]
    exact dvd_mul_right _ _
  have hcdP := factors_modEq hPca hPda
  have hsum : a + Q * r ≡ b + Q * s [MOD P] := by
    simpa only [← hr, ← hs, Nat.add_sub_of_le (by omega : a ≤ c),
      Nat.add_sub_of_le (by omega : b ≤ d)] using hcdP
  have heq := Nat.ModEq.cancel_left_of_coprime
    (Nat.coprime_pow_primes α₄ β₁ hp hq hpq) (habP.add_left_cancel hsum)
  exact hrs.ne (heq.eq_of_lt_of_lt (hrs.trans hsP) hsP)

end MetaMathlibExt
