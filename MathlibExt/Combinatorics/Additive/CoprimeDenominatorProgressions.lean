/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Rify

/-!
# Rational progressions with coprime denominators
-/

namespace MetaMathlibExt

/-- **No integer points for coprime denominators, the first at least 3.** Let
$s_1, s_2, p_1, p_2, q_1, q_2$ be natural numbers with $\gcd(p_1, q_1) = 1$, $\gcd(q_1, q_2) = 1$
and $q_1 \ge 3$, and let $x = s_1 + p_1/q_1$ and $d = s_2 + p_2/q_2$. Then for all natural numbers
$i$ and $j$, neither $x + id$ nor $2x + jd$ is a nonnegative integer.

The paper's further hypotheses ($p_1, p_2, q_2 > 0$, $\gcd(p_2, q_2) = 1$, $d \notin \mathbb{N}$)
are not needed and are not stated ($p_1 > 0$ and $q_2 > 0$ already follow from the two coprimality
conditions and $q_1 \ge 3$).

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 18
(`integers-2026-A58-lem-18`). -/
public theorem add_mul_not_mem_nat_of_coprime_den (x d : ℝ) (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ)
    (hc₁ : Nat.Coprime p₁ q₁) (hq : Nat.Coprime q₁ q₂) (hq₁ : 3 ≤ q₁)
    (hx : x = s₁ + (p₁ : ℝ) / q₁) (hd : d = s₂ + (p₂ : ℝ) / q₂) (i j : ℕ) :
    x + i * d ∉ Set.range ((↑) : ℕ → ℝ) ∧ 2 * x + j * d ∉ Set.range ((↑) : ℕ → ℝ) := by
  have hq₂' : q₂ ≠ 0 := by
    rintro rfl
    simp at hq
    omega
  have exclude (k t : ℕ) (hk : 0 < k) (hkq : k < q₁) :
      (k : ℝ) * x + t * d ∉ Set.range ((↑) : ℕ → ℝ) := by
    rintro ⟨n, hn⟩
    rw [hx, hd] at hn
    field_simp [show q₁ ≠ 0 by omega, hq₂'] at hn
    -- After clearing denominators, every term except k * p₁ * q₂ is a multiple of q₁.
    have heq : q₁ * ((k * s₁ + t * s₂) * q₂ + t * p₂) + k * (p₁ * q₂) = q₁ * (n * q₂) := by
      rify
      linear_combination -hn
    have hdiv : q₁ ∣ k * (p₁ * q₂) := by
      apply (Nat.dvd_add_right (Nat.dvd_mul_right q₁ _)).mp
      rw [heq]
      exact Nat.dvd_mul_right _ _
    have hdk : q₁ ∣ k := (hc₁.symm.mul_right hq).dvd_of_dvd_mul_right hdiv
    exact hkq.not_ge (Nat.le_of_dvd hk hdk)
  exact ⟨by simpa using exclude 1 i (by decide) (by omega),
    by simpa using exclude 2 j (by decide) (by omega)⟩

private theorem eq_of_add_mul_rat_mem_nat_aux (x d : ℝ) (s p q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q) (i j : ℕ)
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ q - 1) (hj₁ : 1 ≤ j) (hj₂ : j ≤ q - 1)
    (hxi : x + i * d ∈ Set.range ((↑) : ℕ → ℝ)) (hxj : x + j * d ∈ Set.range ((↑) : ℕ → ℝ)) :
    i = j := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have no_lt {k l : ℕ} (hk : 1 ≤ k) (hl : l ≤ q - 1) (hkl : k < l)
      (hxk : x + k * d ∈ Set.range ((↑) : ℕ → ℝ))
      (hxl : x + l * d ∈ Set.range ((↑) : ℕ → ℝ)) : False := by
    obtain ⟨a, ha⟩ := hxk
    obtain ⟨b, hb⟩ := hxl
    let t := l - k
    have ht : 0 < t := Nat.sub_pos_of_lt hkl
    have htq : t < q := by dsimp [t]; omega
    have hl' : (l : ℝ) = k + t := by
      exact_mod_cast (Nat.add_sub_of_le hkl.le).symm
    have hdiff : (b : ℝ) - a = (t : ℝ) * d := by
      rw [hl'] at hb
      linear_combination hb - ha
    -- Clear the denominator in the difference of the two natural-number points.
    rw [hd] at hdiff
    field_simp [hq'] at hdiff
    have heq : q * (a + t * s) + t * p = q * b := by
      rify
      linear_combination -hdiff
    have hdvp : q ∣ t * p := by
      apply (Nat.dvd_add_right (Nat.dvd_mul_right q _)).mp
      rw [heq]
      exact Nat.dvd_mul_right _ _
    exact htq.not_ge (Nat.le_of_dvd ht (hcop.symm.dvd_of_dvd_mul_right hdvp))
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (no_lt hi₁ hj₂ hij hxi hxj).elim
  · exact hij
  · exact (no_lt hj₁ hi₂ hji hxj hxi).elim

/-- **Uniqueness of a nonnegative integer point for a rational difference.** Let $x$ be a real
number, let $s, p, q$ be natural numbers with $0 < p < q$ and $\gcd(p, q) = 1$, and let
$d = s + p/q$. If $i, j \in \{1, \dots, q - 1\}$ and $x + id$ and $x + jd$ are both nonnegative
integers, then $i = j$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 11
(`integers-2026-A58-lem-11`). -/
public theorem eq_of_add_mul_rat_mem_nat (x d : ℝ) (s p q : ℕ) (hp : 0 < p) (hpq : p < q)
    (hcop : Nat.Coprime p q)
    (hd : d = s + (p : ℝ) / q) (i j : ℕ)
    (hi₁ : 1 ≤ i) (hi₂ : i ≤ q - 1) (hj₁ : 1 ≤ j) (hj₂ : j ≤ q - 1)
    (hxi : x + i * d ∈ Set.range ((↑) : ℕ → ℝ)) (hxj : x + j * d ∈ Set.range ((↑) : ℕ → ℝ)) :
    i = j :=
  eq_of_add_mul_rat_mem_nat_aux x d s p q (hp.trans hpq) hcop hd i j hi₁ hi₂ hj₁ hj₂ hxi hxj

/-- **Uniqueness of integer points when the denominators share a factor.** Let
$s_1, s_2, p_1, p_2, q_1, q_2$ be natural numbers with $p_1, p_2 > 0$, $\gcd(p_1, q_1) = 1$,
$\gcd(p_2, q_2) = 1$ and $\gcd(q_1, q_2) > 1$, and let $x = s_1 + p_1/q_1$ and
$d = s_2 + p_2/q_2$. For indices $i, i', j, j' \in \{1, \dots, q_2 - 1\}$: if $x + id$ and
$x + i'd$ are both nonnegative integers then $i = i'$; if $2x + jd$ and $2x + j'd$ are both
nonnegative integers then $j = j'$; and if $x + id$ and $2x + jd$ are both nonnegative integers
then $i \ne j$.

Source: Manish Kumar, Mohan, and Ram Krishna Pandey, *The Union of Two Arithmetic Progressions
with Different Common Differences Is Not an MSTD Set*, INTEGERS 26 (2026), Article A58, Lemma 20
(`integers-2026-A58-lem-20`). -/
public theorem add_mul_mem_nat_unique_of_one_lt_gcd (x d : ℝ) (s₁ s₂ p₁ p₂ q₁ q₂ : ℕ)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂)
    (hc₁ : Nat.Coprime p₁ q₁) (hc₂ : Nat.Coprime p₂ q₂) (hl : 1 < Nat.gcd q₁ q₂)
    (hx : x = s₁ + (p₁ : ℝ) / q₁) (hd : d = s₂ + (p₂ : ℝ) / q₂) :
    (∀ i i' : ℕ, 1 ≤ i → i ≤ q₂ - 1 → 1 ≤ i' → i' ≤ q₂ - 1 →
      x + i * d ∈ Set.range ((↑) : ℕ → ℝ) → x + i' * d ∈ Set.range ((↑) : ℕ → ℝ) → i = i') ∧
    (∀ j j' : ℕ, 1 ≤ j → j ≤ q₂ - 1 → 1 ≤ j' → j' ≤ q₂ - 1 →
      2 * x + j * d ∈ Set.range ((↑) : ℕ → ℝ) → 2 * x + j' * d ∈ Set.range ((↑) : ℕ → ℝ) → j = j') ∧
    (∀ i j : ℕ, 1 ≤ i → i ≤ q₂ - 1 → 1 ≤ j → j ≤ q₂ - 1 →
      x + i * d ∈ Set.range ((↑) : ℕ → ℝ) → 2 * x + j * d ∈ Set.range ((↑) : ℕ → ℝ) → i ≠ j) := by
  -- Keep the source's positive-numerator hypotheses in the public statement.
  clear hp₁ hp₂
  by_cases hq₂ : q₂ = 0
  · -- The index window is empty when the step denominator is zero.
    refine ⟨?_, ?_, ?_⟩ <;> (intro i j hi hi'; omega)
  have hq₂pos : 0 < q₂ := Nat.pos_of_ne_zero hq₂
  refine ⟨eq_of_add_mul_rat_mem_nat_aux x d s₂ p₂ q₂ hq₂pos hc₂ hd,
    eq_of_add_mul_rat_mem_nat_aux (2 * x) d s₂ p₂ q₂ hq₂pos hc₂ hd, ?_⟩
  rintro i j hi hi' _ _ ⟨a, ha⟩ ⟨b, hb⟩ hij
  subst j
  by_cases hq₁ : q₁ = 0
  · -- Lean reads the fraction with denominator zero as zero. An integral start
    -- then forces the index of any integer point to be a multiple of q₂.
    have hx₀ : x = (s₁ : ℝ) := by simpa [hq₁] using hx
    have hq₂' : (q₂ : ℝ) ≠ 0 := by exact_mod_cast hq₂
    rw [hx₀, hd] at ha
    field_simp [hq₂'] at ha
    have heq : q₂ * (s₁ + i * s₂) + i * p₂ = q₂ * a := by
      rify
      linear_combination -ha
    have hdvp : q₂ ∣ i * p₂ := by
      apply (Nat.dvd_add_right (Nat.dvd_mul_right q₂ _)).mp
      rw [heq]
      exact Nat.dvd_mul_right _ _
    have hdiv : q₂ ∣ i := hc₂.symm.dvd_of_dvd_mul_right hdvp
    have hle := Nat.le_of_dvd (by omega : 0 < i) hdiv
    omega
  · -- Equal indices make x the difference of two integer points.
    have hq₁' : (q₁ : ℝ) ≠ 0 := by exact_mod_cast hq₁
    have hdiff : (b : ℝ) = a + x := by linear_combination hb - ha
    rw [hx] at hdiff
    field_simp [hq₁'] at hdiff
    have heq : q₁ * (a + s₁) + p₁ = q₁ * b := by
      rify
      linear_combination -hdiff
    have hdvp : q₁ ∣ p₁ := by
      apply (Nat.dvd_add_right (Nat.dvd_mul_right q₁ _)).mp
      rw [heq]
      exact Nat.dvd_mul_right _ _
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hq₁) (Nat.gcd_dvd_left q₁ q₂)
    have hgcd : Nat.gcd p₁ q₁ = 1 := hc₁
    have hdiv : q₁ ∣ Nat.gcd p₁ q₁ := Nat.dvd_gcd hdvp dvd_rfl
    rw [hgcd] at hdiv
    have hone : q₁ = 1 := Nat.dvd_one.mp hdiv
    omega

end MetaMathlibExt
