/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.TwoNearPerfectOmittedDivisors

/-!
# 2-near perfect `2^k p^2` with omitted divisors `p^m` and `2^b p^j`

This module proves that a `2`-near perfect number of the form `2^k p^2` with `p` an odd
prime and omitted divisors `p^m` and `2^b p^j` (where `m, j ∈ {1, 2}` and `1 ≤ b ≤ k`) is
`200`. The proof follows the paper's case analysis on the omitted divisors. Private
auxiliary lemmas rule out integers strictly between consecutive squares, extract square
cofactors from even powers of two, rule out squares congruent to `2` or `3` modulo `4`,
and bound a positive divisor by its multiple.

Statements from Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua
Zelinsky, *On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61 (arXiv:2310.01305).
-/

namespace MetaMathlibExt

private theorem not_isSquare_of_between_consec_sq {a D : ℤ} (h1 : a ^ 2 < D)
    (h2 : D < (a + 1) ^ 2) : ¬ IsSquare D := by
  rintro ⟨s, hs⟩
  have h1' : a ^ 2 < s ^ 2 := by
    rw [hs, ← pow_two] at h1
    exact h1
  have h2' : s ^ 2 < (a + 1) ^ 2 := by
    rw [hs, ← pow_two] at h2
    exact h2
  have g1 : |a| < |s| := sq_lt_sq.mp h1'
  have g2 : |s| < |a + 1| := sq_lt_sq.mp h2'
  have hle : |a + 1| ≤ |a| + 1 := by
    have h := abs_add_le a (1 : ℤ)
    simpa using h
  omega

private theorem isSquare_of_sq_eq_two_pow_mul {e : ℕ} {D0 s : ℤ}
    (h : s ^ 2 = (2 : ℤ) ^ (2 * e) * D0) : IsSquare D0 := by
  suffices key : ∀ (e : ℕ) (s : ℤ), s ^ 2 = (2 : ℤ) ^ (2 * e) * D0 → IsSquare D0
    from key e s h
  intro e
  induction e with
  | zero =>
    intro s h
    simp at h
    exact ⟨s, by rw [← pow_two]; exact h.symm⟩
  | succ e ih =>
    intro s h
    have hexp : (2 : ℤ) ^ (2 * (e + 1)) = 4 * (2 : ℤ) ^ (2 * e) := by
      rw [show 2 * (e + 1) = 2 * e + 2 by ring, pow_add]
      ring
    have h4 : (4 : ℤ) ∣ s ^ 2 := ⟨(2 : ℤ) ^ (2 * e) * D0, by rw [h, hexp]; ring⟩
    have hseven : Even s := by
      rcases Int.even_or_odd s with hev | hodd
      · exact hev
      · exfalso
        obtain ⟨m, hm⟩ := hodd
        obtain ⟨t, ht⟩ := h4
        have e : s ^ 2 = 4 * (m ^ 2) + 4 * m + 1 := by rw [hm]; ring
        omega
    obtain ⟨s1, hs1⟩ := hseven
    have heq := h
    rw [hs1] at heq
    have b1 : (s1 + s1) ^ 2 = 4 * s1 ^ 2 := by ring
    have b2 : (2 : ℤ) ^ (2 * (e + 1)) * D0 = 4 * ((2 : ℤ) ^ (2 * e) * D0) := by
      rw [hexp]
      ring
    have h1 : s1 ^ 2 = (2 : ℤ) ^ (2 * e) * D0 := by omega
    exact ih s1 h1

private theorem not_isSquare_of_eq_four_mul_add {D s X r : ℤ} (hr : r = 2 ∨ r = 3)
    (hsq : D = s ^ 2) (hform : D = 4 * X + r) : False := by
  subst hsq
  rcases Int.even_or_odd s with hev | hodd
  · obtain ⟨t, ht⟩ := hev
    have b1 : s ^ 2 = 4 * (t ^ 2) := by rw [ht]; ring
    omega
  · obtain ⟨t, ht⟩ := hodd
    have b1 : s ^ 2 = 4 * (t ^ 2) + 4 * t + 1 := by rw [ht]; ring
    omega

private theorem le_of_dvd_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (h : a ∣ b) :
    a ≤ b := by
  obtain ⟨t, ht⟩ := h
  have ht1 : 1 ≤ t := by
    by_contra hcon
    have ht0 : t ≤ 0 := by omega
    have hle := mul_le_mul_of_nonneg_left ht0 (le_of_lt ha)
    omega
  calc a = a * 1 := by ring
    _ ≤ a * t := mul_le_mul_of_nonneg_left ht1 (le_of_lt ha)
    _ = b := ht.symm

/-- **$2$-near perfect $2^k p^2$ with omitted divisors $p^m$ and $2^b p^j$.** Let $p$ be an odd
prime, let each of $m$ and $j$ be $1$ or $2$, and let $b, k$ be integers with $1 \le b \le k$.
If $n = 2^k p^2$ satisfies $\sigma(n) = 2n + p^m + 2^b p^j$, where $\sigma$ is the
sum-of-divisors function (that is, $n$ is $2$-near perfect with omitted divisors $p^m$ and
$2^b p^j$), then $n = 200$.

Source: Vedant Aryan, Dev Madhavani, Savan Parikh, Ingrid Slattery and Joshua Zelinsky,
*On 2-Near Perfect Numbers*, INTEGERS 24 (2024), Article A61, Proposition 4
(`integers-2024-A61-prop-4`). -/
public theorem two_near_perfect_two_pow_mul_prime_sq_case_five {k p m b j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hm : m = 1 ∨ m = 2) (hb : 1 ≤ b) (hbk : b ≤ k)
    (hj : j = 1 ∨ j = 2)
    (hσ : ArithmeticFunction.sigma 1 (2 ^ k * p ^ 2) =
      2 * (2 ^ k * p ^ 2) + p ^ m + 2 ^ b * p ^ j) :
    2 ^ k * p ^ 2 = 200 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hm2 : m ≤ 2 := by omega
  have hj2 : j ≤ 2 := by omega
  have hd₁ : p ^ m ∣ 2 ^ k * p ^ 2 :=
    dvd_trans (pow_dvd_pow _ hm2) (dvd_mul_left _ _)
  have hd₂ : 2 ^ b * p ^ j ∣ 2 ^ k * p ^ 2 :=
    mul_dvd_mul (pow_dvd_pow _ hbk) (pow_dvd_pow _ hj2)
  have hne : p ^ m ≠ 2 ^ b * p ^ j := by
    have h1 : Odd (p ^ m) := hodd.pow
    have h2e : Even (2 ^ b) := Nat.even_pow.mpr ⟨⟨1, rfl⟩, by omega⟩
    have h2 : Even (2 ^ b * p ^ j) := h2e.mul_right _
    obtain ⟨m1, hm1⟩ := h1
    obtain ⟨m2, hm2⟩ := h2
    intro hcon
    rw [hcon] at hm1
    omega
  have hsum := (omitted_divisors_sum_two_pow_mul_prime_sq hp hp2 hd₁ hd₂ hne hσ).1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hsum
  rcases hm with rfl | rfl
  · rcases hj with rfl | rfl
    · simp only [pow_one] at hsum
      have hsq2 : (2 * (p : ℤ) + (2 + (2 : ℤ) ^ b - (2 : ℤ) ^ (k + 1))) ^ 2
          = (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ (k + 1) - 2 * (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ b
            + (2 : ℤ) ^ b * (2 : ℤ) ^ b + 4 * (2 : ℤ) ^ b := by
        linear_combination 4 * hsum
      have hVpos : (0 : ℤ) < (2 : ℤ) ^ b := pow_pos (show (0 : ℤ) < 2 by decide) b
      have key1 : ((2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ (k + 1) - 2 * (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ b
          + (2 : ℤ) ^ b * (2 : ℤ) ^ b + 4 * (2 : ℤ) ^ b)
          - ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b) ^ 2 = 4 * (2 : ℤ) ^ b := by ring
      have hlower : ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b) ^ 2
          < (2 * (p : ℤ) + (2 + (2 : ℤ) ^ b - (2 : ℤ) ^ (k + 1))) ^ 2 := by omega
      rcases lt_or_eq_of_le hbk with hlt | heq
      · have hbk1 : b ≤ k - 1 := by omega
        have hk2 : 2 ≤ k := by omega
        have hU4 : (2 : ℤ) ^ (k + 1) = 4 * (2 : ℤ) ^ (k - 1) := by
          rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
          ring
        have hVW : (2 : ℤ) ^ b ≤ (2 : ℤ) ^ (k - 1) :=
          pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by decide) hbk1
        have hW : (0 : ℤ) < (2 : ℤ) ^ (k - 1) :=
          pow_pos (show (0 : ℤ) < 2 by decide) _
        have key2 : (((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 1) ^ 2)
            - ((2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ (k + 1) - 2 * (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ b
              + (2 : ℤ) ^ b * (2 : ℤ) ^ b + 4 * (2 : ℤ) ^ b)
            = 2 * (2 : ℤ) ^ (k + 1) - 6 * (2 : ℤ) ^ b + 1 := by ring
        have hupper : (2 * (p : ℤ) + (2 + (2 : ℤ) ^ b - (2 : ℤ) ^ (k + 1))) ^ 2
            < ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 1) ^ 2 := by omega
        have hnsq := not_isSquare_of_between_consec_sq hlower hupper
        exact (hnsq ⟨_, pow_two _⟩).elim
      · rw [heq] at hsq2 hb hbk
        have hUV : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := pow_succ' 2 k
        have hV2 : (2 : ℤ) ≤ (2 : ℤ) ^ k := by
          have h := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by decide) (show 1 ≤ k by omega)
          simpa only [pow_one] using h
        have key3 : ((2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ (k + 1) - 2 * (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ k
            + (2 : ℤ) ^ k * (2 : ℤ) ^ k + 4 * (2 : ℤ) ^ k)
            - ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ k + 1) ^ 2
            = 6 * (2 : ℤ) ^ k - 2 * (2 : ℤ) ^ (k + 1) - 1 := by ring
        have hlower' : ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ k + 1) ^ 2
            < (2 * (p : ℤ) + (2 + (2 : ℤ) ^ k - (2 : ℤ) ^ (k + 1))) ^ 2 := by omega
        have key4 : (((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ k + 1 + 1) ^ 2)
            - ((2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ (k + 1) - 2 * (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ k
              + (2 : ℤ) ^ k * (2 : ℤ) ^ k + 4 * (2 : ℤ) ^ k)
            = 4 * (2 : ℤ) ^ (k + 1) - 8 * (2 : ℤ) ^ k + 4 := by ring
        have hupper' : (2 * (p : ℤ) + (2 + (2 : ℤ) ^ k - (2 : ℤ) ^ (k + 1))) ^ 2
            < ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ k + 1 + 1) ^ 2 := by omega
        have hnsq := not_isSquare_of_between_consec_sq hlower' hupper'
        exact (hnsq ⟨_, pow_two _⟩).elim
    · simp only [pow_one] at hsum
      have hsq2 : (2 * (1 + (2 : ℤ) ^ b) * (p : ℤ) + (2 - (2 : ℤ) ^ (k + 1))) ^ 2
          = (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ (k + 1)
            + 4 * (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ b - 4 * (2 : ℤ) ^ b := by
        linear_combination 4 * (1 + (2 : ℤ) ^ b) * hsum
      have hU2 : (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ (k + 1) = (2 : ℤ) ^ (2 * k + 2) := by
        have hexp : (k + 1) + (k + 1) = 2 * k + 2 := by ring
        rw [← pow_add, hexp]
      rcases Nat.even_or_odd b with hbeven | hbodd
      · obtain ⟨r, hr⟩ := hbeven
        have e1 : (2 : ℤ) ^ (2 * (r + 1)) * (2 : ℤ) ^ (2 * k - b)
            = (2 : ℤ) ^ (2 * k + 2) := by
          have hexp : 2 * (r + 1) + (2 * k - b) = 2 * k + 2 := by omega
          rw [← pow_add, hexp]
        have e2 : (2 : ℤ) ^ (2 * (r + 1)) * (2 : ℤ) ^ (k + 1)
            = 4 * (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ b := by
          have hexp : 2 * (r + 1) + (k + 1) = 2 + (k + 1) + b := by omega
          rw [← pow_add, hexp, pow_add, pow_add]
          ring
        have hP : (2 : ℤ) ^ (2 * (r + 1)) = 4 * (2 : ℤ) ^ b := by
          have hexp : 2 * (r + 1) = 2 + b := by omega
          rw [hexp, pow_add]
          ring
        have hfact : (2 * (1 + (2 : ℤ) ^ b) * (p : ℤ) + (2 - (2 : ℤ) ^ (k + 1))) ^ 2
            = (2 : ℤ) ^ (2 * (r + 1))
              * ((2 : ℤ) ^ (2 * k - b) + (2 : ℤ) ^ (k + 1) - 1) := by
          linear_combination hsq2 - e1 - e2 + hU2 + hP
        obtain ⟨s0, hs0⟩ := isSquare_of_sq_eq_two_pow_mul (e := r + 1) hfact
        rw [← pow_two] at hs0
        have hexp1 : (2 : ℤ) ^ (2 * k - b) = 4 * (2 : ℤ) ^ (2 * k - b - 2) := by
          have h2k : 2 ≤ 2 * k - b := by omega
          have e : 2 * k - b = (2 * k - b - 2) + 2 := by omega
          conv_lhs => rw [e, pow_add]
          ring
        have hexp2 : (2 : ℤ) ^ (k + 1) = 4 * (2 : ℤ) ^ (k - 1) := by
          rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
          ring
        have hform : (2 : ℤ) ^ (2 * k - b) + (2 : ℤ) ^ (k + 1) - 1
            = 4 * ((2 : ℤ) ^ (2 * k - b - 2) + (2 : ℤ) ^ (k - 1) - 1) + 3 := by
          rw [hexp1, hexp2]
          ring
        exact (not_isSquare_of_eq_four_mul_add (Or.inr rfl) hs0 hform).elim
      · obtain ⟨r, hr⟩ := hbodd
        have e1 : (2 : ℤ) ^ (2 * (r + 1)) * (2 : ℤ) ^ (2 * k - b + 1)
            = (2 : ℤ) ^ (2 * k + 2) := by
          have hexp : 2 * (r + 1) + (2 * k - b + 1) = 2 * k + 2 := by omega
          rw [← pow_add, hexp]
        have e2 : (2 : ℤ) ^ (2 * (r + 1)) * (2 : ℤ) ^ (k + 2)
            = 4 * (2 : ℤ) ^ (k + 1) * (2 : ℤ) ^ b := by
          have hexp : 2 * (r + 1) + (k + 2) = 2 + (k + 1) + b := by omega
          rw [← pow_add, hexp, pow_add, pow_add]
          ring
        have hP : (2 : ℤ) ^ (2 * (r + 1)) = 2 * (2 : ℤ) ^ b := by
          have hexp : 2 * (r + 1) = 1 + b := by omega
          rw [hexp, pow_add]
          ring
        have hfact : (2 * (1 + (2 : ℤ) ^ b) * (p : ℤ) + (2 - (2 : ℤ) ^ (k + 1))) ^ 2
            = (2 : ℤ) ^ (2 * (r + 1))
              * ((2 : ℤ) ^ (2 * k - b + 1) + (2 : ℤ) ^ (k + 2) - 2) := by
          linear_combination hsq2 - e1 - e2 + hU2 + 2 * hP
        obtain ⟨s0, hs0⟩ := isSquare_of_sq_eq_two_pow_mul (e := r + 1) hfact
        rw [← pow_two] at hs0
        have hexp1 : (2 : ℤ) ^ (2 * k - b + 1) = 4 * (2 : ℤ) ^ (2 * k - b + 1 - 2) := by
          have h2k : 2 ≤ 2 * k - b + 1 := by omega
          have e : 2 * k - b + 1 = (2 * k - b + 1 - 2) + 2 := by omega
          conv_lhs => rw [e, pow_add]
          ring
        have hexp2 : (2 : ℤ) ^ (k + 2) = 4 * (2 : ℤ) ^ k := by
          rw [pow_add]
          ring
        have hform : (2 : ℤ) ^ (2 * k - b + 1) + (2 : ℤ) ^ (k + 2) - 2
            = 4 * ((2 : ℤ) ^ (2 * k - b + 1 - 2) + (2 : ℤ) ^ k - 1) + 2 := by
          rw [hexp1, hexp2]
          ring
        exact (not_isSquare_of_eq_four_mul_add (Or.inl rfl) hs0 hform).elim
  · rcases hj with rfl | rfl
    · simp only [pow_one] at hsum
      rcases lt_or_eq_of_le hb with hb1 | rfl
      · have hb2 : 2 ≤ b := by omega
        have hsq2 : (((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) - 4 * (p : ℤ)) ^ 2
            = ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
              + 8 * ((2 : ℤ) ^ (k + 1) - 1) := by
          linear_combination 8 * hsum
        have hsqwit : IsSquare (((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
            + 8 * ((2 : ℤ) ^ (k + 1) - 1)) := by
          refine ⟨((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) - 4 * (p : ℤ), ?_⟩
          rw [← pow_two]
          exact hsq2.symm
        have hV4 : (4 : ℤ) ≤ (2 : ℤ) ^ b := by
          have h := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by decide) hb2
          have e : (2 : ℤ) ^ 2 = 4 := by decide
          omega
        have hUeven : Even ((2 : ℤ) ^ (k + 1)) := ⟨(2 : ℤ) ^ k, by rw [pow_succ']; ring⟩
        have hVeven : Even ((2 : ℤ) ^ b) := by
          have e : (2 : ℤ) ^ b = 2 * (2 : ℤ) ^ (b - 1) := by
            rw [show b = (b - 1) + 1 by omega]
            exact pow_succ' 2 _
          exact ⟨(2 : ℤ) ^ (b - 1), by omega⟩
        obtain ⟨ru, hu⟩ := hUeven
        obtain ⟨rv, hv⟩ := hVeven
        have hBodd : Odd ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) :=
          ⟨ru - rv - 1, by omega⟩
        have hDodd : Odd (((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
            + 8 * ((2 : ℤ) ^ (k + 1) - 1)) :=
          hBodd.pow.add_even ⟨4 * ((2 : ℤ) ^ (k + 1) - 1), by ring⟩
        have key1 : (((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
            + 8 * ((2 : ℤ) ^ (k + 1) - 1))
            - ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3) ^ 2
            = 8 * (2 : ℤ) ^ b - 16 := by ring
        have hgt : ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3) ^ 2
            < ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
              + 8 * ((2 : ℤ) ^ (k + 1) - 1) := by omega
        have hceven : Even ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3 + 1) :=
          ⟨ru - rv + 2, by omega⟩
        have hsqeven : Even ((((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3 + 1)) ^ 2) := by
          obtain ⟨t, ht⟩ := hceven
          exact ⟨2 * t ^ 2, by rw [ht]; ring⟩
        have h1le : ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3 + 1) ^ 2
            ≤ ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
              + 8 * ((2 : ℤ) ^ (k + 1) - 1) := by
          by_contra hcon
          have hlt : ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
              + 8 * ((2 : ℤ) ^ (k + 1) - 1)
              < ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3 + 1) ^ 2 := by omega
          exact (not_isSquare_of_between_consec_sq hgt hlt) hsqwit
        have hne : ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3 + 1) ^ 2
            ≠ ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
              + 8 * ((2 : ℤ) ^ (k + 1) - 1) := by
          intro hcon
          rw [hcon] at hsqeven
          obtain ⟨q1, hq1⟩ := hsqeven
          obtain ⟨q2, hq2⟩ := hDodd
          omega
        have hmid : ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3 + 1) ^ 2
            < ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
              + 8 * ((2 : ℤ) ^ (k + 1) - 1) :=
          lt_of_le_of_ne h1le hne
        have h2le : ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3 + 1 + 1) ^ 2
            ≤ ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
              + 8 * ((2 : ℤ) ^ (k + 1) - 1) := by
          by_contra hcon
          have hlt : ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
              + 8 * ((2 : ℤ) ^ (k + 1) - 1)
              < ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3 + 1 + 1) ^ 2 := by omega
          exact (not_isSquare_of_between_consec_sq hmid hlt) hsqwit
        have key2 : (((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b - 1) ^ 2
            + 8 * ((2 : ℤ) ^ (k + 1) - 1))
            - ((2 : ℤ) ^ (k + 1) - (2 : ℤ) ^ b + 3 + 1 + 1) ^ 2
            = -4 * (2 : ℤ) ^ (k + 1) + 12 * (2 : ℤ) ^ b - 32 := by ring
        have h38 : 3 * (2 : ℤ) ^ b ≥ (2 : ℤ) ^ (k + 1) + 8 := by omega
        have h4V : (2 : ℤ) ^ (k + 1) < 4 * (2 : ℤ) ^ b := by omega
        have hbk' : b = k := by
          have e1 : (2 : ℤ) ^ (b + 2) = 4 * (2 : ℤ) ^ b := by rw [pow_add]; ring
          have hlt : (2 : ℤ) ^ (k + 1) < (2 : ℤ) ^ (b + 2) := by omega
          have hlt2 : k + 1 < b + 2 := by
            by_contra hcon
            have hle : b + 2 ≤ k + 1 := by omega
            have hpow := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by decide) hle
            omega
          omega
        rw [hbk'] at hsum
        have hUV : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := pow_succ' 2 k
        rw [hUV] at hsum
        have h24 : (2 : ℤ) ^ k * ((p : ℤ) + 2) = 2 * (p : ℤ) ^ 2 + (p : ℤ) + 1 := by
          linear_combination -hsum
        have hdiv : ((p : ℤ) + 2) ∣ 2 * (p : ℤ) ^ 2 + (p : ℤ) + 1 :=
          ⟨(2 : ℤ) ^ k, by linear_combination -h24⟩
        have h7 : ((p : ℤ) + 2) ∣ 7 := by
          obtain ⟨t, ht⟩ := hdiv
          refine ⟨t + (3 - 2 * (p : ℤ)), by linear_combination ht⟩
        have hle : (p : ℤ) + 2 ≤ 7 := le_of_dvd_pos (by omega) (by decide) h7
        have hp3 : 3 ≤ p := by
          have h2 := hp.two_le
          omega
        have hp5 : p ≤ 5 := by omega
        interval_cases p
        · exact absurd h7 (by decide)
        · exact absurd h7 (by decide)
        · have hV8 : (2 : ℤ) ^ k = 8 := by omega
          have hk1 : 1 ≤ k := by omega
          have hk3 : k ≤ 3 := by
            by_contra hcon
            have h4 : 4 ≤ k := by omega
            have hpow := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by decide) (show 4 ≤ k by omega)
            have e16 : (2 : ℤ) ^ 4 = 16 := by decide
            omega
          interval_cases k
          · exact absurd hV8 (by decide)
          · exact absurd hV8 (by decide)
          · decide
      · simp only [pow_one] at hsum
        have hfactor : ((p : ℤ) + 1) * (2 * (p : ℤ) - ((2 : ℤ) ^ (k + 1) - 1)) = 0 := by
          linear_combination hsum
        have hp1 : (p : ℤ) + 1 ≠ 0 := by omega
        have h2p : 2 * (p : ℤ) - ((2 : ℤ) ^ (k + 1) - 1) = 0 := by
          rcases mul_eq_zero.mp hfactor with h | h
          · omega
          · exact h
        have eU : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := pow_succ' 2 k
        omega
    · have h25 : (2 : ℤ) ^ (k + 1) * ((p : ℤ) + 1)
          = 2 * (p : ℤ) ^ 2 + (2 : ℤ) ^ b * (p : ℤ) ^ 2 + (p : ℤ) + 1 := by
        linear_combination -hsum
      have hdiv1 : ((p : ℤ) + 1)
          ∣ 2 * (p : ℤ) ^ 2 + (2 : ℤ) ^ b * (p : ℤ) ^ 2 + (p : ℤ) + 1 :=
        ⟨(2 : ℤ) ^ (k + 1), by linear_combination -h25⟩
      have hdiv2 : ((p : ℤ) + 1) ∣ (p : ℤ) ^ 2 * (2 + (2 : ℤ) ^ b) := by
        obtain ⟨t, ht⟩ := hdiv1
        refine ⟨t - 1, by linear_combination ht⟩
      have hdiv3 : ((p : ℤ) + 1) ∣ 2 + (2 : ℤ) ^ b := by
        obtain ⟨t, ht⟩ := hdiv2
        refine ⟨(2 + (2 : ℤ) ^ b) * (1 - (p : ℤ)) + t, by linear_combination ht⟩
      obtain ⟨z, hz⟩ := hdiv3
      have hz' : z * ((p : ℤ) + 1) = 2 + (2 : ℤ) ^ b := by linear_combination -hz
      have hVpos : (0 : ℤ) < (2 : ℤ) ^ b := pow_pos (show (0 : ℤ) < 2 by decide) b
      have hp3 : 3 ≤ p := by
        have h2 := hp.two_le
        omega
      have hzpos : 0 < z := by
        by_contra hcon
        have hz0 : z ≤ 0 := by omega
        have hle := mul_nonpos_of_nonpos_of_nonneg hz0 (show (0 : ℤ) ≤ (p : ℤ) + 1 by omega)
        omega
      have hp1even : Even ((p : ℤ) + 1) := by
        obtain ⟨r, hr⟩ := hodd
        exact ⟨(r : ℤ) + 1, by omega⟩
      have hzodd : Odd z := by
        rcases Int.even_or_odd z with hzeven | hodd'
        · exfalso
          obtain ⟨z2, hz2⟩ := hzeven
          obtain ⟨w, hw⟩ := hp1even
          have h4 : (4 : ℤ) ∣ 2 + (2 : ℤ) ^ b := by
            have h41 : (4 : ℤ) ∣ z * ((p : ℤ) + 1) := ⟨z2 * w, by rw [hz2, hw]; ring⟩
            rw [hz'] at h41
            exact h41
          have hexp : (2 : ℤ) ^ b = 2 * (2 : ℤ) ^ (b - 1) := by
            rw [show b = (b - 1) + 1 by omega]
            exact pow_succ' 2 _
          obtain ⟨t, ht⟩ := h4
          have hodd1 : Odd ((2 : ℤ) ^ (b - 1)) := ⟨t - 1, by omega⟩
          have hb10 : b - 1 = 0 := by
            by_contra hcon
            have h1 : 1 ≤ b - 1 := by omega
            have hexp2 : (2 : ℤ) ^ (b - 1) = 2 * (2 : ℤ) ^ (b - 2) := by
              rw [show b - 1 = (b - 2) + 1 by omega]
              exact pow_succ' 2 _
            obtain ⟨m, hm⟩ := hodd1
            omega
          have hb1 : b = 1 := by omega
          subst hb1
          simp only [pow_one] at h25
          have hdiv1' : ((p : ℤ) + 1) ∣ 4 * (p : ℤ) ^ 2 + (p : ℤ) + 1 :=
            ⟨(2 : ℤ) ^ (k + 1), by linear_combination -h25⟩
          have h4' : ((p : ℤ) + 1) ∣ 4 := by
            obtain ⟨t, ht⟩ := hdiv1'
            refine ⟨t - (4 * (p : ℤ) - 3), by linear_combination ht⟩
          have hle4 : (p : ℤ) + 1 ≤ 4 := le_of_dvd_pos (by omega) (by decide) h4'
          have hp3eq : p = 3 := by omega
          subst hp3eq
          simp only [Nat.cast_ofNat] at h25
          have e4 : (2 : ℤ) ^ (k + 1) = 4 * (2 : ℤ) ^ (k - 1) := by
            rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
            ring
          omega
        · exact hodd'
      have hpowdvd : (2 : ℤ) ^ b ∣ (2 : ℤ) ^ (k + 1) * ((p : ℤ) + 1) :=
        dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : b ≤ k + 1)) _
      rw [h25] at hpowdvd
      have h_dvd_pow : (2 : ℤ) ^ b ∣ 2 * (p : ℤ) ^ 2 + (p : ℤ) + 1 := by
        obtain ⟨t, ht⟩ := hpowdvd
        refine ⟨t - (p : ℤ) ^ 2, by linear_combination ht⟩
      have hp23 : 23 < p := by
        by_contra hcon
        have hle23 : p ≤ 23 := by omega
        have hppos : (0 : ℤ) < (p : ℤ) := by omega
        have hsqpos : (0 : ℤ) < (p : ℤ) ^ 2 := pow_pos hppos 2
        have hNpos : (0 : ℤ) < 2 * (p : ℤ) ^ 2 + (p : ℤ) + 1 := by omega
        have hleN := le_of_dvd_pos hVpos hNpos h_dvd_pow
        have hp2sq : (p : ℤ) ^ 2 ≤ 529 := by
          have h := pow_le_pow_left₀ (show (0 : ℤ) ≤ (p : ℤ) by omega)
            (show (p : ℤ) ≤ 23 by omega) 2
          have e : (23 : ℤ) ^ 2 = 529 := by decide
          omega
        have hV1082 : (2 : ℤ) ^ b ≤ 1082 := by omega
        have hb10 : b ≤ 10 := by
          by_contra hcon2
          have h11 : 11 ≤ b := by omega
          have hpow := pow_le_pow_right₀ (show (1 : ℤ) ≤ 2 by decide) h11
          have e2048 : (2 : ℤ) ^ 11 = 2048 := by decide
          omega
        have hk1gen : 1 ≤ k := by omega
        have e4 : (2 : ℤ) ^ (k + 1) = 4 * (2 : ℤ) ^ (k - 1) := by
          rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
          ring
        interval_cases p <;> interval_cases b <;>
          (first | exact absurd hp (by decide) | omega)
      have hz'' : z * (p : ℤ) + z - 2 = (2 : ℤ) ^ b := by linear_combination hz'
      have h28 : z * (p : ℤ) + z - 2 ∣ 4 * (z + 2 * (p : ℤ) - 1) := by
        obtain ⟨w, hw⟩ := h_dvd_pow
        refine ⟨2 * z * w - (4 * (p : ℤ) - 2),
          by linear_combination 2 * z * hw - 2 * z * w * hz''⟩
      have hapos : (0 : ℤ) < z * (p : ℤ) + z - 2 := by
        rw [hz'']
        exact hVpos
      have hcpos : (0 : ℤ) < 4 * (z + 2 * (p : ℤ) - 1) := by omega
      have h28copy := h28
      obtain ⟨mm, hmm⟩ := h28
      have hm1 : 1 ≤ mm := by
        by_contra hcon
        have hm0 : mm ≤ 0 := by omega
        have hle := mul_le_mul_of_nonneg_left hm0 (le_of_lt hapos)
        omega
      have hmcases : mm = 1 ∨ 2 ≤ mm := by omega
      rcases hmcases with rfl | hm2
      · have hac : z * (p : ℤ) + z - 2 = 4 * (z + 2 * (p : ℤ) - 1) := by omega
        have heqz : z * ((p : ℤ) - 3) = 8 * (p : ℤ) - 2 := by linear_combination hac
        have hpne3 : p ≠ 3 := by
          rintro rfl
          simp only [Nat.cast_ofNat] at heqz
          rw [sub_self, mul_zero] at heqz
          omega
        have hdiv22 : ((p : ℤ) - 3) ∣ 8 * (p : ℤ) - 2 := ⟨z, by linear_combination -heqz⟩
        have h22 : ((p : ℤ) - 3) ∣ 22 := by
          obtain ⟨t, ht⟩ := hdiv22
          refine ⟨t - 8, by linear_combination ht⟩
        have hle22 : (p : ℤ) - 3 ≤ 22 := le_of_dvd_pos (by omega) (by decide) h22
        have hple25 : p ≤ 25 := by omega
        have hp24 : 24 ≤ p := by omega
        interval_cases p <;> exact absurd hp (by decide)
      · have h2a : 2 * (z * (p : ℤ) + z - 2) ≤ 4 * (z + 2 * (p : ℤ) - 1) := by
          have hle := mul_le_mul_of_nonneg_left hm2 (le_of_lt hapos)
          omega
        have hle : z * ((p : ℤ) - 1) ≤ 4 * (p : ℤ) := by
          have e : z * ((p : ℤ) - 1) = z * (p : ℤ) - z := by ring
          rw [e]
          omega
        have h5 : 4 * (p : ℤ) ≤ 5 * ((p : ℤ) - 1) := by omega
        have hz5 : z ≤ 5 := le_of_mul_le_mul_right (le_trans hle h5) (by omega)
        obtain ⟨zm, hzm⟩ := hzodd
        have hzcases : z = 1 ∨ z = 3 ∨ z = 5 := by omega
        rcases hzcases with rfl | rfl | rfl
        · have e1 : (1 : ℤ) * (p : ℤ) + 1 - 2 = (p : ℤ) - 1 := by ring
          have e2 : 4 * ((1 : ℤ) + 2 * (p : ℤ) - 1) = 8 * (p : ℤ) := by ring
          rw [e1, e2] at h28copy
          have h8 : ((p : ℤ) - 1) ∣ 8 := by
            obtain ⟨t, ht⟩ := h28copy
            refine ⟨t - 8, by linear_combination ht⟩
          have hle8 : (p : ℤ) - 1 ≤ 8 := le_of_dvd_pos (by omega) (by decide) h8
          omega
        · have e1 : (3 : ℤ) * (p : ℤ) + 3 - 2 = 3 * (p : ℤ) + 1 := by ring
          have e2 : 4 * ((3 : ℤ) + 2 * (p : ℤ) - 1) = 8 * (p : ℤ) + 8 := by ring
          rw [e1, e2] at h28copy
          have h16 : 3 * (p : ℤ) + 1 ∣ 16 := by
            obtain ⟨t, ht⟩ := h28copy
            refine ⟨3 * t - 8, by linear_combination 3 * ht⟩
          have hle16 : 3 * (p : ℤ) + 1 ≤ 16 := le_of_dvd_pos (by omega) (by decide) h16
          omega
        · have e1 : (5 : ℤ) * (p : ℤ) + 5 - 2 = 5 * (p : ℤ) + 3 := by ring
          have e2 : 4 * ((5 : ℤ) + 2 * (p : ℤ) - 1) = 8 * (p : ℤ) + 16 := by ring
          rw [e1, e2] at h28copy
          have h56 : 5 * (p : ℤ) + 3 ∣ 56 := by
            obtain ⟨t, ht⟩ := h28copy
            refine ⟨5 * t - 8, by linear_combination 5 * ht⟩
          have hle56 : 5 * (p : ℤ) + 3 ≤ 56 := le_of_dvd_pos (by omega) (by decide) h56
          omega

end MetaMathlibExt
