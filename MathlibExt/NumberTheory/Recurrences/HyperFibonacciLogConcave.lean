/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import MathlibExt.NumberTheory.Recurrences.GeneralizedHyperFibonacci
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Eventual log-concavity of generalized hyper-Fibonacci numbers

This module proves that the generalized hyper-Fibonacci numbers `W_{p,n}^{(r)}` of order `r ≥ 1`
with `p ≥ 1`, `a ≥ 0` and `b > 0` are eventually positive and log-concave
(`generalizedHyperFibonacci_eventually_logConcave`), Corollary 10 of Abdelhak Taane,
Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of Toeplitz Matrices Involving
Generalized Hyper-Fibonacci Numbers*, Journal of Integer Sequences 29 (2026), Article 26.2.5.
In particular the hyper `p`-Fibonacci numbers `F_{p,n}^{(r)}` and the hyper `p`-Lucas numbers
`L_{p,n}^{(r)}` of order `r ≥ 1` are eventually positive and log-concave
(`hyperPFibonacci_hyperPLucas_eventually_logConcave`), Corollary 11 of the same paper.

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

end hyperPFibonacci_hyperPLucas_eventually_logConcave

open hyperPFibonacci_hyperPLucas_eventually_logConcave in
/-- **Eventual log-concavity of generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers
with $p \ge 1$, $a \ge 0$ and $b > 0$, let $W^{(r)}_{p,n}$ denote the generalized hyper-Fibonacci
numbers, and let $r \ge 1$ be a natural number. Then there is a natural number $N$ such that for
every $n \ge N$ we have $W^{(r)}_{p,n} > 0$ and
$W^{(r)}_{p,n} W^{(r)}_{p,n+2} \le (W^{(r)}_{p,n+1})^2$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Corollary 10 (`jis-2026-26.2.5-cor-10`). -/
public theorem generalizedHyperFibonacci_eventually_logConcave (p a b : ℤ)
    (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 < b) (r : ℕ) (hr : 1 ≤ r) :
    ∃ N : ℕ, ∀ n ≥ N, 0 < generalizedHyperFibonacci p a b r n ∧
      generalizedHyperFibonacci p a b r n * generalizedHyperFibonacci p a b r (n + 2) ≤
        generalizedHyperFibonacci p a b r (n + 1) ^ 2 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
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
        generalizedHyperFibonacci p 2 p r (n + 1) ^ 2) :=
  ⟨generalizedHyperFibonacci_eventually_logConcave p 0 1 hp le_rfl one_pos r hr,
    generalizedHyperFibonacci_eventually_logConcave p 2 p hp zero_le_two
      (lt_of_lt_of_le one_pos hp) r hr⟩

namespace generalizedHyperFibonacci_hankel_det

open hyperPFibonacci_hyperPLucas_eventually_logConcave
open Polynomial Matrix Finset

/-- The moment functional sends `X ^ k` to the `k`th entry of a sequence. -/
private noncomputable def moment (u : ℕ → ℤ) : ℤ[X] →ₗ[ℤ] ℤ :=
  (basisMonomials ℤ).constr ℤ u

private theorem moment_monomial (u : ℕ → ℤ) (k : ℕ) (c : ℤ) :
    moment u (monomial k c) = c * u k := by
  have h : (X : ℤ[X]) ^ k = basisMonomials ℤ k := by
    rw [coe_basisMonomials]
    change X ^ k = monomial k 1
    rw [← C_mul_X_pow_eq_monomial, map_one, one_mul]
  rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, h, map_smul]
  exact congrArg (c * ·) ((basisMonomials ℤ).constr_basis ℤ u k)

/-- Multiplying by `X - p` takes the weighted forward difference of the moments. -/
private noncomputable def step (p : ℤ) : ℤ[X] := X - C p

private theorem moment_step (p : ℤ) (u : ℕ → ℤ) (f : ℤ[X]) :
    moment u (step p * f) = moment (fun k => u (k + 1) - p * u k) f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [mul_add, map_add, hf, hg, map_add]
  | monomial k c =>
    change moment u ((X - C p) * monomial k c) = _
    rw [sub_mul, map_sub, ← monomial_one_one_eq_X, ← monomial_zero_left,
      monomial_mul_monomial, monomial_mul_monomial]
    simp only [moment_monomial, one_mul, zero_add, Nat.add_comm 1 k]
    ring

/-- The ordinary sequence satisfies the recurrence with characteristic polynomial `q`. -/
private noncomputable def q (p : ℤ) : ℤ[X] := X ^ 2 - (C p * X + 1)

private theorem moment_q (p : ℤ) (u : ℕ → ℤ) (f : ℤ[X]) :
    moment u (q p * f) = moment (fun k => u (k + 2) - p * u (k + 1) - u k) f := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [mul_add, map_add, hf, hg, map_add]
  | monomial k c =>
    have hq : q p = monomial 2 1 - (monomial 1 p + 1) := by
      change X ^ 2 - (C p * X + 1) = _
      simp [C_mul_X_pow_eq_monomial.symm]
    rw [hq, sub_mul, add_mul, one_mul, map_sub, map_add,
      monomial_mul_monomial, monomial_mul_monomial]
    simp only [moment_monomial, one_mul, Nat.add_comm 2 k, Nat.add_comm 1 k]
    ring

private theorem moments_X (u : ℕ → ℤ) (i : ℕ) : moment u (X ^ i) = u i := by
  have h : monomial i (1 : ℤ) = X ^ i := by rw [← C_mul_X_pow_eq_monomial, map_one, one_mul]
  rw [← h, moment_monomial, one_mul]

private theorem moment_hyper_step (p a b : ℤ) (r n : ℕ) (f : ℤ[X]) :
    moment (fun k => generalizedHyperFibonacci p a b (r + 1) (n + k)) (step p * f) =
      moment (fun k => generalizedHyperFibonacci p a b r (n + 1 + k)) f := by
  rw [moment_step]
  have h (k : ℕ) : generalizedHyperFibonacci p a b (r + 1) (n + (k + 1)) -
      p * generalizedHyperFibonacci p a b (r + 1) (n + k) =
      generalizedHyperFibonacci p a b r (n + 1 + k) := by
    rw [← Nat.add_assoc, generalizedHyperFibonacci_succ_succ, add_sub_cancel_left,
      Nat.add_right_comm n k 1]
  simp only [h]

private theorem moment_hyper_steps (p a b : ℤ) (i r n : ℕ) (f : ℤ[X]) :
    moment (fun k => generalizedHyperFibonacci p a b (r + i) (n + k)) (step p ^ i * f) =
      moment (fun k => generalizedHyperFibonacci p a b r (n + i + k)) f := by
  induction i generalizing n with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', mul_assoc, ← Nat.add_assoc, moment_hyper_step, ih,
      show n + 1 + i = n + (i + 1) by omega]

private theorem order_one_gap (p a b : ℤ) (n : ℕ) :
    generalizedPFibonacci p a b (n + 2) - generalizedHyperFibonacci p a b 1 n =
      p ^ (n + 1) * b := by
  induction n with
  | zero =>
    rw [(generalizedHyperFibonacci_zero_one p a b 1).1, W_succ_succ]
    change p * b + a - a = p ^ 1 * b
    ring
  | succ n ih =>
    rw [show n + 1 + 2 = n + 2 + 1 by omega, W_succ_succ p a b (n + 1),
      generalizedHyperFibonacci_succ_succ]
    change p * generalizedPFibonacci p a b (n + 2) + generalizedPFibonacci p a b (n + 1) -
      (p * generalizedHyperFibonacci p a b 1 n + generalizedPFibonacci p a b (n + 1)) = _
    rw [pow_succ]
    linear_combination p * ih

private theorem moment_hyper_zero_q (p a b : ℤ) (n : ℕ) (f : ℤ[X]) :
    moment (fun k => generalizedHyperFibonacci p a b 0 (n + k)) (q p * f) = 0 := by
  rw [moment_q]
  have h : (fun k => generalizedHyperFibonacci p a b 0 (n + (k + 2)) -
      p * generalizedHyperFibonacci p a b 0 (n + (k + 1)) -
      generalizedHyperFibonacci p a b 0 (n + k)) = 0 := by
    funext k
    change generalizedPFibonacci p a b (n + (k + 2)) -
      p * generalizedPFibonacci p a b (n + (k + 1)) - generalizedPFibonacci p a b (n + k) = 0
    rw [← Nat.add_assoc, W_succ_succ, Nat.add_assoc]
    ring
  rw [h]
  induction f using Polynomial.induction_on' with
  | add f g hf hg => rw [map_add, hf, hg, add_zero]
  | monomial k c => simp [moment_monomial]

private theorem moment_hyper_one_q (p a b : ℤ) (n : ℕ) :
    moment (fun k => generalizedHyperFibonacci p a b 1 (n + k)) (q p) = p ^ (n + 1) * b := by
  rw [← mul_one (q p), moment_q, ← pow_zero (X : ℤ[X]), moments_X]
  simp only [zero_add, generalizedHyperFibonacci_succ_succ p a b 0 (n + 1),
    ← Nat.add_assoc n 1 1, add_sub_cancel_left]
  exact order_one_gap p a b n

/-- A degree-ordered monic basis has a unit lower triangular coefficient matrix. -/
private theorem det_coeff {m : ℕ} (f : Fin m → ℤ[X])
    (hf : ∀ i, (f i).Monic ∧ (f i).natDegree = i) :
    (Matrix.of fun i j : Fin m => (f i).coeff j).det = 1 := by
  have htri : (Matrix.of fun i j : Fin m => (f i).coeff j).IsLowerTriangular := by
    intro i j hij
    exact coeff_eq_zero_of_natDegree_lt (by rw [(hf i).2]; exact hij)
  rw [det_of_isLowerTriangular _ htri]
  have hd (i : Fin m) : (f i).coeff i = 1 := by
    rw [← (hf i).2]
    exact (hf i).1.coeff_natDegree
  simp [hd]

private theorem sum_monomials {m : ℕ} (f : ℤ[X]) (h : f.natDegree < m) :
    f = ∑ i : Fin m, monomial i (f.coeff i) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => monomial i (f.coeff i))]
  calc
    f = ∑ i ∈ range (f.natDegree + 1), monomial i (f.coeff i) := by
      simpa only [C_mul_X_pow_eq_monomial] using f.as_sum_range_C_mul_X_pow
    _ = ∑ i ∈ range m, monomial i (f.coeff i) := by
      apply sum_subset (range_mono (by omega))
      intro i _ hi
      rw [mem_range, not_lt] at hi
      rw [coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < i), monomial_zero_right]

/-- Changing either monomial basis to a degree-ordered monic basis preserves the Hankel
determinant. -/
private theorem det_moment_basis {m : ℕ} (u : ℕ → ℤ) (f g : Fin m → ℤ[X])
    (hf : ∀ i, (f i).Monic ∧ (f i).natDegree = i)
    (hg : ∀ i, (g i).Monic ∧ (g i).natDegree = i) :
    (Matrix.of fun i j : Fin m => moment u (f i * g j)).det =
      (Matrix.of fun i j : Fin m => u (i + j)).det := by
  let F : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i j => (f i).coeff j
  let G : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i j => (g i).coeff j
  let M : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun i j => u (i + j)
  have hM : (Matrix.of fun i j : Fin m => moment u (f i * g j)) = F * (M * Gᵀ) := by
    ext i j
    change moment u (f i * g j) = (F * (M * Gᵀ)) i j
    conv_lhs =>
      rw [sum_monomials (f i) (by simpa only [(hf i).2] using i.isLt),
        sum_monomials (g j) (by simpa only [(hg j).2] using j.isLt)]
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum, monomial_mul_monomial, moment_monomial,
      Matrix.mul_apply, F, G, M, transpose_apply, of_apply]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => by ring
  rw [hM, det_mul, det_mul, det_transpose, det_coeff f hf, det_coeff g hg, one_mul, mul_one]

private theorem q_low_degree (p : ℤ) : (C p * X + 1 : ℤ[X]).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
  have h : (C p * (X : ℤ[X])).natDegree ≤ (C p).natDegree + (X : ℤ[X]).natDegree :=
    natDegree_mul_le
  simpa using h

private theorem q_monic (p : ℤ) : (q p).Monic := by
  apply monic_X_pow_sub
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast (show _ < 2 from
    lt_of_le_of_lt (q_low_degree p) (by decide)))

private theorem q_degree (p : ℤ) : (q p).natDegree = 2 := by
  change (X ^ 2 - (C p * X + 1)).natDegree = 2
  rw [natDegree_sub_eq_left_of_natDegree_lt (by
    simpa using lt_of_le_of_lt (q_low_degree p) (by decide : 1 < 2))]
  simp

/-- The last two row polynomials are `(X - p)^r` and `X * (X - p)^r`. -/
private noncomputable def rowBasis (p : ℤ) (r i : ℕ) : ℤ[X] :=
  if i ≤ r then step p ^ i else X * step p ^ r

/-- The first two column polynomials are `1` and `X`; the rest are multiples of `q`. -/
private noncomputable def colBasis (p : ℤ) : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | j + 2 => step p ^ j * q p

private theorem step_degree (p : ℤ) (i : ℕ) : (step p ^ i).natDegree = i := by
  change ((X - C p) ^ i).natDegree = i
  rw [(monic_X_sub_C p).natDegree_pow, natDegree_X_sub_C, mul_one]

private theorem row_monic (p : ℤ) (r : ℕ) (i : Fin (r + 2)) :
    (rowBasis p r i).Monic ∧ (rowBasis p r i).natDegree = i := by
  have h (k : ℕ) : (step p ^ k).Monic := (monic_X_sub_C p).pow k
  let f : ℤ[X] := if (i : ℕ) ≤ r then step p ^ (i : ℕ) else X * step p ^ r
  change f.Monic ∧ f.natDegree = i
  dsimp only [f]
  by_cases hi : (i : ℕ) ≤ r
  · rw [ite_eq_left hi, step_degree]
    exact ⟨h _, rfl⟩
  · rw [ite_eq_right hi, monic_X.natDegree_mul (h r), natDegree_X, step_degree]
    exact ⟨monic_X.mul (h r), by have := i.isLt; omega⟩

private theorem col_monic (p : ℤ) (j : ℕ) :
    (colBasis p j).Monic ∧ (colBasis p j).natDegree = j := by
  match j with
  | 0 => exact ⟨monic_one, natDegree_one⟩
  | 1 => exact ⟨monic_X, natDegree_X⟩
  | j + 2 =>
    have h : (step p ^ j).Monic := (monic_X_sub_C p).pow j
    exact ⟨h.mul (q_monic p), by
      change (step p ^ j * q p).natDegree = j + 2
      rw [h.natDegree_mul (q_monic p), step_degree, q_degree]⟩

/-- Reversing `m + 1` indices is reversal of the first `m`, followed by one rotation. -/
private theorem revPerm_succ (m : ℕ) :
    (Fin.revPerm : Equiv.Perm (Fin (m + 1))) = finRotate (m + 1) *
      (finSumFinEquiv (m := m) (n := 1)).permCongr
        (Fin.revPerm.sumCongr (1 : Equiv.Perm (Fin 1))) := by
  apply Equiv.ext
  intro i
  obtain ⟨x, rfl⟩ := (finSumFinEquiv (m := m) (n := 1)).surjective i
  cases x with
  | inl j =>
    rw [Equiv.Perm.mul_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change (Fin.castAdd 1 j).rev = finRotate (m + 1) (Fin.castAdd 1 j.rev)
    have hj : Fin.castAdd 1 j.rev =
        (⟨j.rev, Nat.lt_succ_of_lt j.rev.isLt⟩ : Fin (m + 1)) := Fin.ext rfl
    rw [hj, finRotate_of_lt j.rev.isLt]
    apply Fin.ext
    simp only [Fin.val_rev, Fin.val_castAdd]
    omega
  | inr j =>
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rw [Equiv.Perm.mul_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change (Fin.last m).rev = finRotate (m + 1) (Fin.last m)
    rw [finRotate_last, Fin.rev_last]

private theorem sign_rev_succ (m : ℕ) :
    (↑(Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 1)))) : ℤ) =
      (-1) ^ m * ↑(Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) := by
  rw [revPerm_succ, Equiv.Perm.sign_mul, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr,
    map_one, mul_one, sign_finRotate, Nat.add_sub_cancel, Units.val_mul, Units.val_pow_eq_pow_val]
  rfl

/-- In the Hankel determinant, column reversal and the shift of the Cassini term together
give the parity prescribed by the formula. -/
private theorem sign_rev_hankel (r : ℕ) :
    (↑(Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (r + 2)))) : ℤ) =
      (-1) ^ (r + (r + 3) / 2) := by
  have hpair (m : ℕ) :
      (↑(Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 2)))) : ℤ) =
        -↑(Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) := by
    rw [sign_rev_succ (m + 1), sign_rev_succ m, pow_succ]
    rcases neg_one_pow_eq_or ℤ m with h | h <;> rw [h] <;> ring
  have h0 : (Fin.revPerm : Equiv.Perm (Fin 0)) = 1 := Equiv.ext fun i => Fin.elim0 i
  induction r using Nat.twoStepInduction with
  | zero => rw [hpair 0, h0]; norm_num
  | one => rw [hpair 1, sign_rev_succ 0, h0]; norm_num
  | more r ih _ =>
    rw [hpair (r + 2), ih, show (r + 2) + (r + 2 + 3) / 2 = r + (r + 3) / 2 + 3 by omega,
      pow_add]
    ring

private theorem row_head (p : ℤ) (r : ℕ) (i : Fin r) :
    rowBasis p r (Fin.castAdd 2 i) = step p ^ (i : ℕ) := by
  change (if (i : ℕ) ≤ r then step p ^ (i : ℕ) else X * step p ^ r) = _
  exact ite_eq_left i.isLt.le

private theorem row_tail (p : ℤ) (r : ℕ) (i : Fin 2) :
    rowBasis p r (Fin.natAdd r i) = X ^ (i : ℕ) * step p ^ r := by
  change (if r + (i : ℕ) ≤ r then step p ^ (r + (i : ℕ)) else X * step p ^ r) = _
  have hi := i.isLt
  rcases (show (i : ℕ) = 0 ∨ (i : ℕ) = 1 by omega) with h | h
  · simp [h]
  · rw [h, ite_eq_right (by omega), pow_one]

private theorem col_rev_head (p : ℤ) (r : ℕ) (j : Fin r) :
    colBasis p (Fin.castAdd 2 j).rev = step p ^ (j.rev : ℕ) * q p := by
  have h : ((Fin.castAdd 2 j).rev : ℕ) = (j.rev : ℕ) + 2 := by
    simp only [Fin.val_rev, Fin.val_castAdd]
    have := j.isLt
    omega
  rw [h]
  delta colBasis
  rfl

private theorem col_rev_tail (p : ℤ) (r : ℕ) (j : Fin 2) :
    colBasis p (Fin.natAdd r j).rev = X ^ (j.rev : ℕ) := by
  have h : ((Fin.natAdd r j).rev : ℕ) = j.rev := by
    simp only [Fin.val_rev, Fin.val_natAdd]
    omega
  rw [h]
  have hj := j.rev.isLt
  rcases (show (j.rev : ℕ) = 0 ∨ (j.rev : ℕ) = 1 by omega) with hh | hh
  · rw [hh, pow_zero]
    delta colBasis
    rfl
  · rw [hh, pow_one]
    delta colBasis
    rfl

private theorem moment_hyper_all_steps (p a b : ℤ) (r n : ℕ) (f : ℤ[X]) :
    moment (fun k => generalizedHyperFibonacci p a b r (n + k)) (step p ^ r * f) =
      moment (fun k => generalizedHyperFibonacci p a b 0 (n + r + k)) f := by
  simpa only [Nat.zero_add] using moment_hyper_steps p a b r 0 n f

private theorem moment_at_least_order (p a b : ℤ) (r n i j : ℕ) (h : r ≤ i + j) :
    moment (fun k => generalizedHyperFibonacci p a b r (n + k))
      (step p ^ i * (step p ^ j * q p)) = 0 := by
  have he : step p ^ (i + j) * q p = step p ^ r * (q p * step p ^ (i + j - r)) := by
    rw [← mul_assoc, mul_comm (step p ^ r) (q p), mul_assoc, ← pow_add,
      show r + (i + j - r) = i + j by omega, mul_comm (q p)]
  rw [← mul_assoc, ← pow_add, he, moment_hyper_all_steps, moment_hyper_zero_q]

private theorem moment_one_before_order (p a b : ℤ) (r n i j : ℕ) (h : i + j + 1 = r) :
    moment (fun k => generalizedHyperFibonacci p a b r (n + k))
      (step p ^ i * (step p ^ j * q p)) = p ^ (n + r) * b := by
  rw [← mul_assoc, ← pow_add, ← h, Nat.add_comm (i + j) 1, moment_hyper_steps, moment_hyper_one_q,
    show n + (i + j) + 1 = n + (1 + (i + j)) by omega]

private theorem moment_bottom_left (p a b : ℤ) (r n i j : ℕ) :
    moment (fun k => generalizedHyperFibonacci p a b r (n + k))
      ((X ^ i * step p ^ r) * (step p ^ j * q p)) = 0 := by
  have he : (X ^ i * step p ^ r) * (step p ^ j * q p) =
      step p ^ r * (q p * (X ^ i * step p ^ j)) := by ac_rfl
  rw [he, moment_hyper_all_steps, moment_hyper_zero_q]

private theorem moment_bottom_right (p a b : ℤ) (r n i j : ℕ) :
    moment (fun k => generalizedHyperFibonacci p a b r (n + k))
      ((X ^ i * step p ^ r) * X ^ j) = generalizedPFibonacci p a b (n + r + (i + j)) := by
  rw [mul_comm (X ^ i), mul_assoc, ← pow_add, moment_hyper_all_steps, moments_X]
  rfl

/-- Reverse the columns after the monic changes of basis. The left block is triangular;
the last two rows see only the ordinary Fibonacci recurrence. -/
private theorem det_reversed_basis (p a b : ℤ) (r n : ℕ) :
    ((Matrix.of fun i j : Fin (r + 2) =>
      moment (fun k => generalizedHyperFibonacci p a b r (n + k))
        (rowBasis p r i * colBasis p j)).submatrix id Fin.revPerm).det =
      (p ^ (n + r) * b) ^ r * ((-1) ^ (n + r) * (b ^ 2 - a * (p * b + a))) := by
  let M : Matrix (Fin (r + 2)) (Fin (r + 2)) ℤ := Matrix.of fun i j =>
    moment (fun k => generalizedHyperFibonacci p a b r (n + k))
      (rowBasis p r i * colBasis p j.rev)
  change M.det = _
  let e : Fin r ⊕ Fin 2 ≃ Fin (r + 2) := finSumFinEquiv
  let A := M.submatrix (Fin.castAdd 2) (Fin.castAdd 2)
  let B := M.submatrix (Fin.castAdd 2) (Fin.natAdd r)
  let D : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of fun i j =>
    generalizedPFibonacci p a b (n + r + ((i : ℕ) + (j.rev : ℕ)))
  have hM : M.submatrix e e = fromBlocks A B 0 D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · rfl
    · change moment (fun k => generalizedHyperFibonacci p a b r (n + k))
        (rowBasis p r (Fin.natAdd r i) * colBasis p (Fin.castAdd 2 j).rev) = 0
      rw [row_tail, col_rev_head, moment_bottom_left]
    · change moment (fun k => generalizedHyperFibonacci p a b r (n + k))
        (rowBasis p r (Fin.natAdd r i) * colBasis p (Fin.natAdd r j).rev) = D i j
      rw [row_tail, col_rev_tail, moment_bottom_right]
      rfl
  have hA (i j : Fin r) : A i j = moment (fun k => generalizedHyperFibonacci p a b r (n + k))
      (step p ^ (i : ℕ) * (step p ^ (j.rev : ℕ) * q p)) := by
    change moment (fun k => generalizedHyperFibonacci p a b r (n + k))
      (rowBasis p r (Fin.castAdd 2 i) * colBasis p (Fin.castAdd 2 j).rev) = _
    rw [row_head, col_rev_head]
  have ht : A.IsUpperTriangular := by
    intro i j h
    rw [hA]
    apply moment_at_least_order
    have hi := i.isLt
    have hj := j.isLt
    change (j : ℕ) < (i : ℕ) at h
    rw [Fin.val_rev]
    omega
  have hd (i : Fin r) : A i i = p ^ (n + r) * b := by
    rw [hA]
    apply moment_one_before_order
    have hi := i.isLt
    rw [Fin.val_rev]
    omega
  have hD : D.det = (-1) ^ (n + r) * (b ^ 2 - a * (p * b + a)) := by
    rw [det_fin_two]
    change generalizedPFibonacci p a b (n + r + 1) *
        generalizedPFibonacci p a b (n + r + 1) - generalizedPFibonacci p a b (n + r + 0) *
        generalizedPFibonacci p a b (n + r + 2) = _
    rw [add_zero, ← pow_two, W_cassini]
  rw [← det_submatrix_equiv_self e, hM, det_fromBlocks_zero₂₁, hD,
    det_of_isUpperTriangular ht]
  simp [hd]

end generalizedHyperFibonacci_hankel_det

open generalizedHyperFibonacci_hankel_det in
/-- **Hankel determinants of generalized hyper-Fibonacci numbers.** Let $p, a, b$ be integers, let
$W^{(r)}_{p,n}$ denote the generalized hyper-Fibonacci numbers and put $\Delta = a^2 + pab - b^2$.
For all natural numbers $r$ and $n$, the $(r+2) \times (r+2)$ Hankel matrix
$H_{r,n} = (W^{(r)}_{p,n+i+j})_{0 \le i, j \le r+1}$ has determinant
$\det H_{r,n} = (-1)^{n+1+\lfloor (r+3)/2 \rfloor} p^{nr+r^2} b^r \Delta$.

Source: Abdelhak Taane, Ihab-Eddine Djellas and Mohammed Mekkaoui, *Total Positivity of
Toeplitz Matrices Involving Generalized Hyper-Fibonacci Numbers*, Journal of Integer
Sequences 29 (2026), Article 26.2.5, Proposition 7, quoting Ait-Amrane et al.
(`jis-2026-26.2.5-prop-7`). -/
public theorem generalizedHyperFibonacci_hankel_det (p a b : ℤ) (r n : ℕ) :
    (Matrix.of fun i j : Fin (r + 2) =>
        generalizedHyperFibonacci p a b r (n + i + j)).det =
      (-1) ^ (n + 1 + (r + 3) / 2) * p ^ (n * r + r ^ 2) * b ^ r * (a ^ 2 + p * a * b - b ^ 2) := by
  let u (k : ℕ) := generalizedHyperFibonacci p a b r (n + k)
  let M : Matrix (Fin (r + 2)) (Fin (r + 2)) ℤ := Matrix.of fun i j =>
    moment u (rowBasis p r i * colBasis p j)
  let R := M.submatrix id Fin.revPerm
  have hInv : R.submatrix id Fin.revPerm = M := by
    ext i j
    change M i j.rev.rev = M i j
    rw [Fin.rev_rev]
  have hM := Matrix.det_permute' Fin.revPerm R
  rw [hInv] at hM
  change M.det = (↑(Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (r + 2)))) : ℤ) * R.det at hM
  have hR : R.det = (p ^ (n + r) * b) ^ r *
      ((-1) ^ (n + r) * (b ^ 2 - a * (p * b + a))) := det_reversed_basis p a b r n
  have hBasis : M.det = (Matrix.of fun i j : Fin (r + 2) =>
      generalizedHyperFibonacci p a b r (n + i + j)).det := by
    simpa only [u, Nat.add_assoc] using
      det_moment_basis u (fun i => rowBasis p r i) (fun j => colBasis p j)
        (row_monic p r) (fun j => col_monic p j)
  rw [← hBasis, hM, hR, sign_rev_hankel, mul_pow, ← pow_mul,
    show (n + r) * r = n * r + r ^ 2 by ring]
  have hsign : (-1 : ℤ) ^ (r + (r + 3) / 2) * (-1) ^ (n + r) =
      (-1) ^ (n + (r + 3) / 2) := by
    rw [← pow_add, show r + (r + 3) / 2 + (n + r) = (n + (r + 3) / 2) + 2 * r by omega,
      pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  calc
    _ = ((-1 : ℤ) ^ (r + (r + 3) / 2) * (-1) ^ (n + r)) *
        (p ^ (n * r + r ^ 2) * b ^ r) * (b ^ 2 - a * (p * b + a)) := by ring
    _ = _ := by
      rw [hsign, show n + 1 + (r + 3) / 2 = (n + (r + 3) / 2) + 1 by omega, pow_succ]
      ring


end MetaMathlibExt
