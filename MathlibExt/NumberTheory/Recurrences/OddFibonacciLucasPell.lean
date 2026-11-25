/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Odd Fibonacci–Lucas values in a Pell equation

Every natural solution of `P² - (a² + 4b) Q² = -4b` for positive integers `a` and `b` with `b ∣ a`
is a rescaled pair of generalized Lucas and Fibonacci values at the same odd index.
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔽[" a ", " b "]" =>
  generalizedFibonacciPolynomial 0 1 (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

local notation "𝕃[" a ", " b "]" =>
  generalizedFibonacciPolynomial 2 (C ((a : ℕ) : ℤ) * X) (C ((a : ℕ) : ℤ) * X) (C ((b : ℕ) : ℤ))

namespace fibLucas_odd_of_pell_eq

private theorem eval_step {a b : ℕ} (p₀ p₁ : ℤ[X]) (n : ℕ) :
    let G := generalizedFibonacciPolynomial p₀ p₁ (C (a : ℤ) * X) (C (b : ℤ))
    (G (n + 2)).eval 1 = a * (G (n + 1)).eval 1 + b * (G n).eval 1 := by
  simp

private theorem lucas_eq {a b : ℕ} (n : ℕ) :
    (𝕃[a, b] n).eval 1 = 2 * (𝔽[a, b] (n + 1)).eval 1 - a * (𝔽[a, b] n).eval 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp; ring
  | more n ih₀ ih₁ =>
    rw [eval_step _ _ n, ih₀, ih₁, eval_step _ _ (n + 1), eval_step _ _ n]
    ring

-- Write P = a q + 2k. The equation becomes b q² = k(k + a q) + b.
-- Reversing two Fibonacci steps takes (q, k) to (r, k - a r), where r = q - (a/b)k.
private theorem descent {a b : ℕ} {c : ℤ} (hb : 0 < (b : ℤ)) (hc : 0 < c)
    (hbc : (b : ℤ) * c = a) (q k : ℤ) (hq : 0 < q) (hk : 0 ≤ k)
    (h : b * q ^ 2 = k * (k + a * q) + b) :
    ∃ n : ℕ, (b : ℤ) ^ n * q = (𝔽[a, b] (2 * n + 1)).eval 1 ∧
      (b : ℤ) ^ n * (k + a * q) = (𝔽[a, b] ((2 * n + 1) + 1)).eval 1 := by
  by_cases hk₀ : k = 0
  · subst k
    have hq₁ : q = 1 := by
      have hs : (b : ℤ) * q ^ 2 = b * 1 := by simpa using h
      have := mul_left_cancel₀ hb.ne' hs
      nlinarith
    exact ⟨0, by simp [hq₁], by simp [hq₁]⟩
  have hkpos : 0 < k := lt_of_le_of_ne hk (Ne.symm hk₀)
  let r := q - c * k
  have hqr : (b : ℤ) * q = b * r + a * k := by
    dsimp [r]
    linear_combination k * hbc
  have hprod : (b : ℤ) * q * r = k ^ 2 + b := by
    linear_combination h - q * hqr
  have hr : 0 < r := (mul_pos_iff_of_pos_left (mul_pos hb hq)).mp (by rw [hprod]; positivity)
  have hrlt : r < q := sub_lt_self _ (mul_pos hc hkpos)
  have hpred : (b : ℤ) * r ^ 2 = k * (k - a * r) + b := by
    linear_combination hprod - r * hqr
  have hkn : 0 ≤ k - a * r := by
    apply nonneg_of_mul_nonneg_right _ hkpos
    have hr₁ : 1 ≤ r := by omega
    nlinarith only [hpred, mul_nonneg hb.le (show 0 ≤ r ^ 2 - 1 by nlinarith)]
  obtain ⟨n, hn, hn'⟩ := descent hb hc hbc r (k - a * r) hr hkn (by
    rw [sub_add_cancel, mul_comm (k - a * r)]
    exact hpred)
  rw [sub_add_cancel] at hn'
  have hnext : (b : ℤ) ^ (n + 1) * q = (𝔽[a, b] ((2 * n + 1) + 2)).eval 1 := by
    rw [eval_step, ← hn', ← hn, pow_succ]
    linear_combination (b : ℤ) ^ n * hqr
  refine ⟨n + 1, ?_, ?_⟩
  · simpa only [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega] using hnext
  · rw [show 2 * (n + 1) + 1 + 1 = ((2 * n + 1) + 1) + 2 by omega, eval_step,
      ← hnext, ← hn', pow_succ]
    ring
termination_by q.toNat
decreasing_by omega

end fibLucas_odd_of_pell_eq

/-- **Pell-type solutions as rescaled odd Fibonacci–Lucas values.** Let $a$ and $b$ be positive
integers with $b \mid a$, and let $F_i(x), L_i(x) \in \mathbb{Z}[x]$ be the polynomials with
$F_0 = 0$, $F_1 = 1$, $L_0 = 2$, $L_1 = ax$ and $G_{i+2} = ax\,G_{i+1} + b\,G_i$ for $G = F, L$
and all $i \ge 0$. If natural numbers $P$ and $Q$ satisfy $P^2 - (a^2 + 4b) Q^2 = -4b$, then
there is $n \in \mathbb{N}$ with $b^n P = L_{2n+1}(1)$ and $b^n Q = F_{2n+1}(1)$.

Source: Yuji Tsuno, *Polynomial Values with Integer Coefficients for the Generating Functions of
Fibonacci Polynomials*, The Fibonacci Quarterly 62 (2024), Article tsuno05142024,
Proposition 2.3 (`fq-2024-tsuno05142024-prop-2.3`). -/
public theorem fibLucas_odd_of_pell_eq {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hba : b ∣ a)
    {P Q : ℕ} (h : (P : ℤ) ^ 2 - (a ^ 2 + 4 * b) * Q ^ 2 = -4 * b) :
    ∃ n : ℕ, (b : ℤ) ^ n * P = (𝕃[a, b] (2 * n + 1)).eval 1 ∧
      (b : ℤ) ^ n * Q = (𝔽[a, b] (2 * n + 1)).eval 1 := by
  have hb' : 0 < (b : ℤ) := by exact_mod_cast hb
  obtain ⟨c, hbc⟩ := hba
  have hc : 0 < c := by
    by_contra! h₀
    simp [show c = 0 by omega] at hbc
    omega
  have hQ : 0 < (Q : ℤ) := by
    by_contra! h₀
    have : Q = 0 := by omega
    subst Q
    simp at h
    nlinarith [sq_nonneg (P : ℤ)]
  have hs : (P : ℤ) ^ 2 = ((a : ℤ) * Q) ^ 2 + 4 * (b * ((Q : ℤ) ^ 2 - 1)) := by
    linear_combination h
  have hle : (a : ℤ) * Q ≤ P := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    nlinarith only [hs, mul_nonneg hb'.le (show 0 ≤ (Q : ℤ) ^ 2 - 1 by nlinarith)]
  have heven : (P : ℤ) % 2 = ((a : ℤ) * Q) % 2 := by
    rw [← Int.sq_emod_two, ← Int.sq_emod_two ((a : ℤ) * Q)]
    omega
  let k := ((P : ℤ) - a * Q) / 2
  have hP : (P : ℤ) = a * Q + 2 * k := by dsimp [k]; omega
  have heq : (b : ℤ) * Q ^ 2 = k * (k + a * Q) + b := by
    rw [hP] at hs
    linarith only [hs]
  obtain ⟨n, hn, hn'⟩ := fibLucas_odd_of_pell_eq.descent (c := c) hb' (by exact_mod_cast hc)
    (by exact_mod_cast hbc.symm) Q k hQ (by dsimp [k]; omega) heq
  refine ⟨n, ?_, hn⟩
  rw [fibLucas_odd_of_pell_eq.lucas_eq, ← hn', ← hn, hP]
  ring

end MetaMathlibExt
