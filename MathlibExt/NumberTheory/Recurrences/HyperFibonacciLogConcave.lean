/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.GeneralizedHyperFibonacci
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Eventual log-concavity of hyper `p`-Fibonacci and hyper `p`-Lucas numbers

This module proves that the hyper `p`-Fibonacci numbers `F_{p,n}^{(r)}` and the hyper `p`-Lucas
numbers `L_{p,n}^{(r)}` of order `r ≥ 1` are eventually positive and log-concave
(`hyperPFibonacci_hyperPLucas_eventually_logConcave`), Corollary 11 of Abdelhak Taane,
Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of Toeplitz Matrices Involving
Generalized Hyper-Fibonacci Numbers*, Journal of Integer Sequences 29 (2026), Article 26.2.5.

`W_{p,n}` is `generalizedPFibonacci p a b n` and `W_{p,n}^{(r)}` is
`generalizedHyperFibonacci p a b r n`; the hyper `p`-Fibonacci and hyper `p`-Lucas numbers are
the cases `(a, b) = (0, 1)` and `(2, p)`.

## Proof

The proof is direct and works for all integers `p ≥ 1`, `a ≥ 0` and `b > 0`. Write `r = s + 1`
and `W_{p,n}^{(r)} = W_{p,n+2r} - p^{n+1} C_n^{(r)}`, where the integers `C_n^{(k)}` satisfy
`C_n^{(0)} = 0`, `C_0^{(k+1)} = C_0^{(k)} + W_{p,2k+1}` and
`C_{n+1}^{(k+1)} = C_n^{(k+1)} + C_{n+1}^{(k)}` (an integer form of the binomial-sum formula
`generalizedHyperFibonacci_sub_eq_sub`). With `C_n = C_n^{(r)}` and `δ_n = C_{n+1}^{(s)}`, an exact
identity writes `(W_{p,n+1}^{(r)})^2 - W_{p,n}^{(r)} W_{p,n+2}^{(r)}` as the sum of the Cassini
term `W_{p,n+2r+1}^2 - W_{p,n+2r} W_{p,n+2r+2} = ±(b^2 - a (p b + a))`, the term
`p^{n+1} (C_n W_{p,n+2s} - 2 p δ_n W_{p,n+2s+1})` and two nonnegative terms. Since
`(n + 1) δ_n ≤ s C_n`, the middle term is eventually at least `W_{p,n+2s}`, which grows without
bound and so eventually exceeds the bounded Cassini term.
-/

namespace MetaMathlibExt

namespace hyperPFibonacci_hyperPLucas_eventually_logConcave

open Finset

/-- The correction term `C_n^{(r)}` of `W_{p,n}^{(r)} = W_{p,n+2r} - p^{n+1} C_n^{(r)}`. -/
private def corr (p a b : ℤ) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | r + 1, n => corr p a b r 0 + generalizedPFibonacci p a b (2 * r + 1) +
      ∑ k ∈ range n, corr p a b r (k + 1)

private theorem corr_zero_left (p a b : ℤ) (n : ℕ) : corr p a b 0 n = 0 := by
  simp only [corr]

private theorem corr_succ_zero (p a b : ℤ) (r : ℕ) :
    corr p a b (r + 1) 0 = corr p a b r 0 + generalizedPFibonacci p a b (2 * r + 1) := by
  simp only [corr, range_zero, sum_empty, add_zero]

private theorem corr_succ_succ (p a b : ℤ) (r n : ℕ) :
    corr p a b (r + 1) (n + 1) = corr p a b (r + 1) n + corr p a b r (n + 1) := by
  simp only [corr, sum_range_succ]
  ring

private theorem W_succ_succ (p a b : ℤ) (n : ℕ) :
    generalizedPFibonacci p a b (n + 2) =
      p * generalizedPFibonacci p a b (n + 1) + generalizedPFibonacci p a b n := rfl

private theorem W_two_mul (p a b : ℤ) (r : ℕ) :
    generalizedPFibonacci p a b (2 * r) = a + p * corr p a b r 0 := by
  induction r with
  | zero => simp only [corr_zero_left, mul_zero, add_zero]; rfl
  | succ r ih =>
    rw [show 2 * (r + 1) = 2 * r + 2 by ring, W_succ_succ, corr_succ_zero, ih]
    ring

/-- The decomposition `W_{p,n}^{(r)} = W_{p,n+2r} - p^{n+1} C_n^{(r)}`. -/
private theorem H_eq (p a b : ℤ) (r n : ℕ) :
    generalizedHyperFibonacci p a b r n =
      generalizedPFibonacci p a b (n + 2 * r) - p ^ (n + 1) * corr p a b r n := by
  induction r generalizing n with
  | zero => simp only [corr_zero_left, mul_zero, sub_zero, add_zero]; rfl
  | succ r hr =>
    induction n with
    | zero =>
      rw [(generalizedHyperFibonacci_zero_one p a b (r + 1)).1, zero_add, W_two_mul]
      ring
    | succ n hn =>
      rw [generalizedHyperFibonacci_succ_succ, hn, hr (n + 1), corr_succ_succ,
        show n + 1 + 2 * (r + 1) = n + 1 + 2 * r + 2 by ring, W_succ_succ,
        show n + 1 + 2 * r + 1 = n + 2 * (r + 1) by ring]
      ring

/-- Cassini's identity for the generalized `p`-Fibonacci sequence. -/
private theorem W_cassini (p a b : ℤ) (m : ℕ) :
    generalizedPFibonacci p a b (m + 1) ^ 2 -
        generalizedPFibonacci p a b m * generalizedPFibonacci p a b (m + 2) =
      (-1) ^ m * (b ^ 2 - a * (p * b + a)) := by
  induction m with
  | zero =>
    change b ^ 2 - a * (p * b + a) = (-1) ^ 0 * (b ^ 2 - a * (p * b + a))
    ring
  | succ m ih =>
    have h1 := W_succ_succ p a b m
    have h2 := W_succ_succ p a b (m + 1)
    linear_combination (-1 : ℤ) * ih + generalizedPFibonacci p a b (m + 2) * h1 -
      generalizedPFibonacci p a b (m + 1) * h2

/-- The algebraic identity behind the eventual log-concavity. -/
private theorem key_identity (p P x y c d d' X₀ X₁ X₂ u₀ u₁ u₂ : ℤ)
    (hX₀ : X₀ = p * y + x) (hX₁ : X₁ = p * X₀ + y) (hX₂ : X₂ = p * X₁ + X₀)
    (hu₀ : u₀ = X₀ - P * c) (hu₁ : u₁ = X₁ - P * p * (c + d))
    (hu₂ : u₂ = X₂ - P * p ^ 2 * (c + d + d')) :
    u₁ ^ 2 - u₀ * u₂ = (X₁ ^ 2 - X₀ * X₂) + P * (c * x - 2 * p * d * y) +
      P ^ 2 * p ^ 2 * d ^ 2 + P * p ^ 2 * (d' - d) * u₀ := by
  subst hu₀ hu₁ hu₂ hX₂ hX₁ hX₀
  ring

variable {p a b : ℤ}

private theorem W_nonneg (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    0 ≤ generalizedPFibonacci p a b n := by
  induction n using Nat.twoStepInduction with
  | zero => exact ha
  | one => exact hb.le
  | more n ih1 ih2 =>
    rw [W_succ_succ]
    have := mul_nonneg (zero_le_one.trans hp) ih2
    linarith

private theorem one_le_W (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    1 ≤ generalizedPFibonacci p a b (n + 1) := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    rw [W_succ_succ]
    have := W_nonneg hp ha hb n
    nlinarith

private theorem W_le_W_succ (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    generalizedPFibonacci p a b (n + 1) ≤ generalizedPFibonacci p a b (n + 2) := by
  rw [W_succ_succ]
  have := W_nonneg hp ha hb n
  have := W_nonneg hp ha hb (n + 1)
  nlinarith

private theorem le_W (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (n : ℕ) :
    (n : ℤ) + 1 ≤ generalizedPFibonacci p a b (n + 2) := by
  induction n with
  | zero =>
    have := one_le_W hp ha hb 0
    have := W_le_W_succ hp ha hb 0
    simp only [Nat.cast_zero, zero_add]
    linarith
  | succ n ih =>
    have h1 := one_le_W hp ha hb n
    have h2 := W_nonneg hp ha hb (n + 2)
    have h3 : generalizedPFibonacci p a b (n + 1 + 2) =
        p * generalizedPFibonacci p a b (n + 2) + generalizedPFibonacci p a b (n + 1) := rfl
    rw [h3]
    push_cast
    nlinarith

private theorem H_nonneg (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r n : ℕ) :
    0 ≤ generalizedHyperFibonacci p a b r n := by
  induction r generalizing n with
  | zero => exact W_nonneg hp ha hb n
  | succ r ih =>
    exact sum_nonneg fun k _ => mul_nonneg (pow_nonneg (zero_le_one.trans hp) _) (ih k)

private theorem one_le_H (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r n : ℕ) :
    1 ≤ generalizedHyperFibonacci p a b r (n + 1) := by
  induction r with
  | zero => exact one_le_W hp ha hb n
  | succ r ih =>
    rw [generalizedHyperFibonacci_succ_succ]
    have := mul_nonneg (zero_le_one.trans hp) (H_nonneg hp ha hb (r + 1) n)
    linarith

private theorem corr_nonneg (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r n : ℕ) :
    0 ≤ corr p a b r n := by
  induction r generalizing n with
  | zero => rw [corr_zero_left]
  | succ r ih =>
    simp only [corr]
    have := W_nonneg hp ha hb (2 * r + 1)
    have := ih 0
    have : 0 ≤ ∑ k ∈ range n, corr p a b r (k + 1) := sum_nonneg fun k _ => ih (k + 1)
    linarith

private theorem one_le_corr (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r n : ℕ) :
    1 ≤ corr p a b (r + 1) n := by
  simp only [corr]
  have := one_le_W hp ha hb (2 * r)
  have := corr_nonneg hp ha hb r 0
  have : 0 ≤ ∑ k ∈ range n, corr p a b r (k + 1) :=
    sum_nonneg fun k _ => corr_nonneg hp ha hb r (k + 1)
  linarith

private theorem corr_le_succ (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r n : ℕ) :
    corr p a b r n ≤ corr p a b r (n + 1) := by
  cases r with
  | zero => rw [corr_zero_left, corr_zero_left]
  | succ r =>
    rw [corr_succ_succ]
    have := corr_nonneg hp ha hb r (n + 1)
    linarith

/-- The growth bound `(n + 1) C_{n+1}^{(r)} ≤ r C_n^{(r+1)}`. -/
private theorem corr_ratio (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r : ℕ) :
    ∀ n : ℕ, ((n : ℤ) + 1) * corr p a b r (n + 1) ≤ (r : ℤ) * corr p a b (r + 1) n := by
  induction r with
  | zero => intro n; simp only [corr_zero_left, mul_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ r ih =>
    intro n
    induction n with
    | zero =>
      have h1 := ih 0
      have h2 := mul_nonneg (Nat.cast_nonneg (α := ℤ) (r + 1))
        (W_nonneg hp ha hb (2 * (r + 1) + 1))
      rw [corr_succ_succ, corr_succ_zero p a b (r + 1)]
      push_cast at h1 h2 ⊢
      nlinarith
    | succ n ihn =>
      have h1 := ih (n + 1)
      rw [corr_succ_succ p a b r (n + 1), corr_succ_succ p a b (r + 1) n]
      push_cast at h1 ihn ⊢
      nlinarith

/-- The coefficient estimate `c ≥ 2 p (p + 1) d + 1` from `(n + 1) d ≤ s c` for large `n`. -/
private theorem coeff_estimate (p c d : ℤ) (s n : ℕ) (hc : 1 ≤ c) (hd : 0 ≤ d)
    (hratio : ((n : ℤ) + 1) * d ≤ (s : ℤ) * c) (hn : 4 * p * (p + 1) * s ≤ (n : ℤ) + 1)
    (hs : s = 0 → d = 0) : 2 * p * (p + 1) * d + 1 ≤ c := by
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · rw [hs h0]
    linarith
  · have hs' : (0 : ℤ) < s := by exact_mod_cast h0
    have h1 : 4 * p * (p + 1) * s * d ≤ ((n : ℤ) + 1) * d := mul_le_mul_of_nonneg_right hn hd
    have h2 : (s : ℤ) * (4 * p * (p + 1) * d) ≤ (s : ℤ) * c := by linarith
    have h3 : 4 * p * (p + 1) * d ≤ c := le_of_mul_le_mul_left h2 hs'
    obtain ⟨t, ht⟩ : ∃ t, t = c - 2 * p * (p + 1) * d := ⟨_, rfl⟩
    have h4 : 1 ≤ 2 * t := by rw [ht]; linarith
    have h5 : 1 ≤ t := by omega
    linarith

/-- The final estimate: the right side of `key_identity` is nonnegative. -/
private theorem final_estimate (p P x y c d e u K Q : ℤ) (hp : 1 ≤ p) (hP : 1 ≤ P)
    (hQ : -|K| ≤ Q) (hx : |K| ≤ x) (hyx : y ≤ (p + 1) * x) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hu : 0 ≤ u) (hcd : 2 * p * (p + 1) * d + 1 ≤ c) :
    0 ≤ Q + P * (c * x - 2 * p * d * y) + P ^ 2 * p ^ 2 * d ^ 2 + P * p ^ 2 * e * u := by
  have hx0 : 0 ≤ x := le_trans (abs_nonneg K) hx
  have hp0 : 0 ≤ p := by linarith
  have hP0 : 0 ≤ P := by linarith
  have h1 : 2 * p * d * y ≤ 2 * p * d * ((p + 1) * x) :=
    mul_le_mul_of_nonneg_left hyx (by positivity)
  have h2 : x * 1 ≤ x * (c - 2 * p * (p + 1) * d) :=
    mul_le_mul_of_nonneg_left (by linarith) hx0
  have h3 : x ≤ c * x - 2 * p * d * y := by linarith
  have h4 : (P - 1) * 0 ≤ (P - 1) * (c * x - 2 * p * d * y) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h5 : 0 ≤ P ^ 2 * p ^ 2 * d ^ 2 := by positivity
  have h6 : 0 ≤ P * p ^ 2 * e * u := by positivity
  linarith

/-- Eventual positivity and log-concavity of `W_{p,n}^{(s+1)}` for `p ≥ 1`, `a ≥ 0`, `b > 0`. -/
private theorem eventually_logConcave (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (s : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci p a b (s + 1) n ∧
      generalizedHyperFibonacci p a b (s + 1) n *
          generalizedHyperFibonacci p a b (s + 1) (n + 2) ≤
        generalizedHyperFibonacci p a b (s + 1) (n + 1) ^ 2 := by
  refine ⟨2 + (4 * p * (p + 1) * s).natAbs + (b ^ 2 - a * (p * b + a)).natAbs,
    fun n hn => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 4 * p * (p + 1) * s + |b ^ 2 - a * (p * b + a)| ≤ (m : ℤ) := by
    have h := (Nat.cast_le (α := ℤ)).mpr hn
    push_cast at h
    have := (4 * p * (p + 1) * s : ℤ).le_natAbs
    rw [Int.natCast_natAbs] at this
    linarith
  refine ⟨lt_of_lt_of_le one_pos (one_le_H hp ha hb (s + 1) (m + 1)), ?_⟩
  change generalizedHyperFibonacci p a b (s + 1) (m + 2) *
      generalizedHyperFibonacci p a b (s + 1) (m + 4) ≤
    generalizedHyperFibonacci p a b (s + 1) (m + 3) ^ 2
  -- The quantities of the identity, at `n = m + 2`.
  have hX₀ : generalizedPFibonacci p a b (m + 2 * s + 4) =
      p * generalizedPFibonacci p a b (m + 2 * s + 3) +
        generalizedPFibonacci p a b (m + 2 * s + 2) := W_succ_succ p a b (m + 2 * s + 2)
  have hX₁ : generalizedPFibonacci p a b (m + 2 * s + 5) =
      p * generalizedPFibonacci p a b (m + 2 * s + 4) +
        generalizedPFibonacci p a b (m + 2 * s + 3) := W_succ_succ p a b (m + 2 * s + 3)
  have hX₂ : generalizedPFibonacci p a b (m + 2 * s + 6) =
      p * generalizedPFibonacci p a b (m + 2 * s + 5) +
        generalizedPFibonacci p a b (m + 2 * s + 4) := W_succ_succ p a b (m + 2 * s + 4)
  have hc₁ : corr p a b (s + 1) (m + 3) = corr p a b (s + 1) (m + 2) + corr p a b s (m + 3) :=
    corr_succ_succ p a b s (m + 2)
  have hc₂ : corr p a b (s + 1) (m + 4) = corr p a b (s + 1) (m + 3) + corr p a b s (m + 4) :=
    corr_succ_succ p a b s (m + 3)
  have hu₀ : generalizedHyperFibonacci p a b (s + 1) (m + 2) =
      generalizedPFibonacci p a b (m + 2 * s + 4) -
        p ^ (m + 3) * corr p a b (s + 1) (m + 2) := by
    rw [H_eq, show m + 2 + 2 * (s + 1) = m + 2 * s + 4 by ring]
  have hu₁ : generalizedHyperFibonacci p a b (s + 1) (m + 3) =
      generalizedPFibonacci p a b (m + 2 * s + 5) -
        p ^ (m + 3) * p * (corr p a b (s + 1) (m + 2) + corr p a b s (m + 3)) := by
    rw [H_eq, show m + 3 + 2 * (s + 1) = m + 2 * s + 5 by ring, hc₁]
    ring
  have hu₂ : generalizedHyperFibonacci p a b (s + 1) (m + 4) =
      generalizedPFibonacci p a b (m + 2 * s + 6) - p ^ (m + 3) * p ^ 2 *
        (corr p a b (s + 1) (m + 2) + corr p a b s (m + 3) + corr p a b s (m + 4)) := by
    rw [H_eq, show m + 4 + 2 * (s + 1) = m + 2 * s + 6 by ring, hc₂, hc₁]
    ring
  have hD := key_identity _ _ _ _ _ _ _ _ _ _ _ _ _ hX₀ hX₁ hX₂ hu₀ hu₁ hu₂
  -- The Cassini term is at least `-|b ^ 2 - a (p b + a)|`.
  have hQ : -|b ^ 2 - a * (p * b + a)| ≤ generalizedPFibonacci p a b (m + 2 * s + 5) ^ 2 -
      generalizedPFibonacci p a b (m + 2 * s + 4) *
        generalizedPFibonacci p a b (m + 2 * s + 6) := by
    have h : generalizedPFibonacci p a b (m + 2 * s + 5) ^ 2 -
        generalizedPFibonacci p a b (m + 2 * s + 4) *
          generalizedPFibonacci p a b (m + 2 * s + 6) =
        (-1) ^ (m + 2 * s + 4) * (b ^ 2 - a * (p * b + a)) :=
      W_cassini p a b (m + 2 * s + 4)
    have h' := neg_abs_le ((-1 : ℤ) ^ (m + 2 * s + 4) * (b ^ 2 - a * (p * b + a)))
    rw [abs_mul, abs_neg_one_pow, one_mul] at h'
    rw [h]
    exact h'
  -- Sizes and signs of the remaining quantities.
  have hx : |b ^ 2 - a * (p * b + a)| ≤ generalizedPFibonacci p a b (m + 2 * s + 2) := by
    have := le_W hp ha hb (m + 2 * s)
    push_cast at this
    have : (0 : ℤ) ≤ 4 * p * (p + 1) * s := by positivity
    linarith
  have hyx : generalizedPFibonacci p a b (m + 2 * s + 3) ≤
      (p + 1) * generalizedPFibonacci p a b (m + 2 * s + 2) := by
    have h := W_le_W_succ hp ha hb (m + 2 * s)
    have hy : generalizedPFibonacci p a b (m + 2 * s + 3) =
        p * generalizedPFibonacci p a b (m + 2 * s + 2) +
          generalizedPFibonacci p a b (m + 2 * s + 1) := W_succ_succ p a b (m + 2 * s + 1)
    rw [hy]
    linarith
  have hcd : 2 * p * (p + 1) * corr p a b s (m + 3) + 1 ≤ corr p a b (s + 1) (m + 2) := by
    refine coeff_estimate p _ _ s (m + 2) (one_le_corr hp ha hb s (m + 2))
      (corr_nonneg hp ha hb s (m + 3)) (corr_ratio hp ha hb s (m + 2)) ?_ ?_
    · have : (0 : ℤ) ≤ |b ^ 2 - a * (p * b + a)| := abs_nonneg _
      push_cast
      linarith
    · intro hs
      rw [hs, corr_zero_left]
  have hfin := final_estimate _ _ _ _ _ _ _ _ _ _ hp (one_le_pow₀ (n := m + 3) hp) hQ hx hyx
    (corr_nonneg hp ha hb s (m + 3)) (sub_nonneg.mpr (corr_le_succ hp ha hb s (m + 3)))
    (H_nonneg hp ha hb (s + 1) (m + 2)) hcd
  rw [← hD] at hfin
  linarith

end hyperPFibonacci_hyperPLucas_eventually_logConcave

open hyperPFibonacci_hyperPLucas_eventually_logConcave in
/-- **Eventual log-concavity of hyper $p$-Fibonacci and hyper $p$-Lucas numbers.** Let
$p \ge 1$ be an integer and $r \ge 1$ a natural number, and let $F_{p,n}^{(r)}$ and
$L_{p,n}^{(r)}$ be the generalized hyper-Fibonacci numbers $W_{p,n}^{(r)}$ with initial values
$(a, b) = (0, 1)$ and $(a, b) = (2, p)$ respectively (the hyper $p$-Fibonacci and hyper
$p$-Lucas numbers). Both sequences are eventually log-concave: there is $N$ such that for all
$n \ge N$, $F_{p,n}^{(r)} > 0$ and $F_{p,n}^{(r)} F_{p,n+2}^{(r)} \le (F_{p,n+1}^{(r)})^2$, and
there is $N'$ such that for all $n \ge N'$, $L_{p,n}^{(r)} > 0$ and
$L_{p,n}^{(r)} L_{p,n+2}^{(r)} \le (L_{p,n+1}^{(r)})^2$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 11 (`jis-2026-26.2.5-cor-11`). -/
public theorem hyperPFibonacci_hyperPLucas_eventually_logConcave (p : ℤ) (hp : 1 ≤ p)
    (r : ℕ) (hr : 1 ≤ r) :
    (∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci p 0 1 r n ∧
      generalizedHyperFibonacci p 0 1 r n * generalizedHyperFibonacci p 0 1 r (n + 2) ≤
        generalizedHyperFibonacci p 0 1 r (n + 1) ^ 2) ∧
    (∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci p 2 p r n ∧
      generalizedHyperFibonacci p 2 p r n * generalizedHyperFibonacci p 2 p r (n + 2) ≤
        generalizedHyperFibonacci p 2 p r (n + 1) ^ 2) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  exact ⟨eventually_logConcave hp le_rfl one_pos s,
    eventually_logConcave hp zero_le_two (lt_of_lt_of_le one_pos hp) s⟩

end MetaMathlibExt
