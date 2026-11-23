/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Primorial
public import MathlibExt.NumberTheory.PrimeInterval.Breusch.ThetaBaseCases
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Breusch primorial and logarithm bounds

The primorial estimate `primorial m ≤ 3.4 ^ m`, certified numerical bounds for
`log 2`, `log 5`, `log 3` and `log 17` with the resulting margin `13`, the
prime-counting bound `π(m) ≤ m / 3`, and gap positivity for `n ≥4762`.
-/

namespace MathlibExt.NumberTheory.BreuschWanted.Internal

open Nat Finset

-- M(t) = (6t)! / ((3t)! (2t)! t !), the multinomial for the 3.4 primorial bound.
/-- **The multinomial coefficient $M(t)$ for the 3.4 primorial bound.** For a natural number
$t$, $M(t) = \frac{(6t)!}{(3t)!\,(2t)!\,t!}$, defined as the quotient of $(6t)!$ by
$(3t)!\,(2t)!\,t!$ in natural-number division. -/
def M34 (t : ℕ) : ℕ := (6*t)! / ((3*t)! * (2*t)! * t !)

/-- **Factorial divisibility behind the multinomial coefficient.** For every natural number $t$,
the product $(3t)!\,(2t)!\,t!$ divides $(6t)!$. -/
lemma M34_dvd (t : ℕ) : (3*t)! * (2*t)! * t ! ∣ (6*t)! := by
  have h1 : (3*t)! * (2*t)! ∣ (5*t)! := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add (3*t) (2*t)
    rwa [show 3*t + 2*t = 5*t by ring] at this
  have h2 : (5*t)! * t ! ∣ (6*t)! := by
    have := Nat.factorial_mul_factorial_dvd_factorial_add (5*t) t
    rwa [show 5*t + t = 6*t by ring] at this
  calc (3*t)! * (2*t)! * t ! = ((3*t)! * (2*t)!) * t ! := by ring
    _ ∣ (5*t)! * t ! := Nat.mul_dvd_mul_right h1 _
    _ ∣ (6*t)! := h2

/-- **Positivity of the multinomial coefficient $M(t)$.** Let $M(t)$ be the natural-number
quotient of $(6t)!$ by $(3t)!\,(2t)!\,t!$. For every natural number $t$, $M(t) > 0$. -/
lemma M34_pos (t : ℕ) : 0 < M34 t := by
  unfold M34
  exact Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) (M34_dvd t)) (by positivity)

/-- **Cleared-denominator identity for the multinomial coefficient $M(t)$.** Let $M(t)$ be the
natural-number quotient of $(6t)!$ by $(3t)!\,(2t)!\,t!$. For every natural number $t$,
$M(t) \cdot \big((3t)!\,(2t)!\,t!\big) = (6t)!$. -/
lemma M34_eq_mul (t : ℕ) : M34 t * ((3*t)! * (2*t)! * t !) = (6*t)! := by
  unfold M34
  exact Nat.div_mul_cancel (M34_dvd t)

-- C(6t,3t) * C(3t,t) = M(t).
/-- **The multinomial coefficient $M(t)$ as a product of binomial coefficients.** Let
$M(t) = \frac{(6t)!}{(3t)!\,(2t)!\,t!}$. For every natural number $t$,
$M(t) = \binom{6t}{3t} \binom{3t}{t}$. -/
lemma M34_eq_choose_mul (t : ℕ) : M34 t = Nat.choose (6*t) (3*t) * Nat.choose (3*t) t := by
  have hX : 0 < (3*t)! * (2*t)! * t ! := by positivity
  apply Nat.mul_right_cancel hX
  rw [M34_eq_mul]
  have e1 : Nat.choose (6*t) (3*t) * ((3*t)! * ((6*t) - (3*t))!) = (6*t)! := by
    rw [← mul_assoc]; exact Nat.choose_mul_factorial_mul_factorial (by omega)
  have e2 : Nat.choose (3*t) t * (t ! * ((3*t) - t)!) = (3*t)! := by
    rw [← mul_assoc]; exact Nat.choose_mul_factorial_mul_factorial (by omega)
  have h63 : (6*t) - (3*t) = 3*t := by omega
  have h32 : (3*t) - t = 2*t := by omega
  rw [h63] at e1; rw [h32] at e2
  -- goal: C(6t,3t)*C(3t,t)*X = (6t)! where X = (3t)!(2t)!t !
  have : Nat.choose (6*t) (3*t) * Nat.choose (3*t) t * ((3*t)! * (2*t)! * t !)
      = (Nat.choose (6*t) (3*t) * ((3*t)! * (3*t)!)) := by
    have h3 : Nat.choose (3*t) t * (t ! * (2*t)!) = (3*t)! := e2
    calc Nat.choose (6*t) (3*t) * Nat.choose (3*t) t * ((3*t)! * (2*t)! * t !)
        = Nat.choose (6*t) (3*t) * ((3*t)! * (Nat.choose (3*t) t * (t ! * (2*t)!))) := by ring
      _ = Nat.choose (6*t) (3*t) * ((3*t)! * (3*t)!) := by rw [h3]
      _ = Nat.choose (6*t) (3*t) * ((3*t)! * (3*t)!) := by ring
  rw [this]; exact e1.symm

-- Central binomial ≤ half of 2^{2m}.
/-- **Half-power bound for the central binomial coefficient.** For every natural number
$m \ge 1$, $\binom{2m}{m} \le 2^{2m-1}$. -/
lemma choose_middle_half {m : ℕ} (hm : 1 ≤ m) : Nat.choose (2*m) m ≤ 2^(2*m-1) := by
  have pascal : Nat.choose (2*m) m
      = Nat.choose (2*m-1) (m-1) + Nat.choose (2*m-1) m := by
    have e := Nat.choose_succ_succ' (2*m-1) (m-1)
    rwa [show (2*m-1)+1 = 2*m by omega, show (m-1)+1 = m by omega] at e
  have symm : Nat.choose (2*m-1) (m-1) = Nat.choose (2*m-1) m := by
    have h := Nat.choose_symm (show m-1 ≤ 2*m-1 by omega)
    rw [show 2*m-1-(m-1) = m by omega] at h
    exact h.symm
  have hsum : Nat.choose (2*m-1) (m-1) + Nat.choose (2*m-1) m
      ≤ ∑ k ∈ Finset.range (2*m), Nat.choose (2*m-1) k := by
    have hsub : ({m-1, m} : Finset ℕ) ⊆ Finset.range (2*m) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_range]
      omega
    have hnn : ∀ k ∈ Finset.range (2*m), k ∉ ({m-1, m} : Finset ℕ) →
        0 ≤ Nat.choose (2*m-1) k :=
      fun k _ _ => Nat.zero_le _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
    rwa [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
      Finset.sum_singleton] at this
  have hpow : ∑ k ∈ Finset.range (2*m), Nat.choose (2*m-1) k = 2^(2*m-1) := by
    have := Nat.sum_range_choose (2*m-1)
    rwa [show 2*m-1+1 = 2*m by omega] at this
  omega

-- (3t)!/(t !)^3 ≤ 3^{3t}, in multiplicative form.
/-- **Multinomial bound for $(3t)!$.** For every natural number $t$,
$(3t)! \le 3^{3t} (t!)^3$. -/
lemma multinomial3_le (t : ℕ) : (3*t)! ≤ 3^(3*t) * (t !)^3 := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    have hexpand : (3*(t+1))! = (3*t+1)*(3*t+2)*(3*t+3)*(3*t)! := by
      have h1 : 3*(t+1) = 3*t+3 := by ring
      rw [h1]
      have e : (3*t+3)! = (3*t+3)*((3*t+2)*((3*t+1)*(3*t)!)) := by
        rw [show 3*t+3 = (3*t+2)+1 by omega, Nat.factorial_succ,
          show 3*t+2 = (3*t+1)+1 by omega, Nat.factorial_succ,
          show 3*t+1 = (3*t)+1 by omega, Nat.factorial_succ]
      rw [e]; ring
    have hpow : (3:ℕ)^(3*(t+1)) = 27 * 3^(3*t) := by
      rw [show 3*(t+1) = 3*t+3 by ring, pow_add]; ring
    have hfact : ((t+1)!) ^ 3 = (t+1)^3 * (t !)^3 := by
      rw [Nat.factorial_succ, mul_pow]
    rw [hexpand, hpow, hfact]
    have hkey : (3*t+1)*(3*t+2)*(3*t+3) ≤ 27*(t+1)^3 := by
      have heq : 27*(t+1)^3 = (3*t+1)*(3*t+2)*(3*t+3) + (27*t^2+48*t+21) := by ring
      omega
    calc (3*t+1)*(3*t+2)*(3*t+3)*(3*t)!
        ≤ (27*(t+1)^3) * (3^(3*t) * (t !)^3) :=
          Nat.mul_le_mul hkey ih
      _ = 27 * 3^(3*t) * ((t+1)^3 * (t !)^3) := by ring

-- C(3t,t)*C(2t,t)*(t !)^3 = (3t)!.
/-- **Binomial factorization of the factorial of a multiple of three.** For every natural
number $t$, $\binom{3t}{t} \binom{2t}{t} (t!)^3 = (3t)!$. -/
lemma choose3_mul_choose2 (t : ℕ) :
    Nat.choose (3*t) t * Nat.choose (2*t) t * (t !)^3 = (3*t)! := by
  have e1 : Nat.choose (3*t) t * (t ! * ((3*t) - t)!) = (3*t)! := by
    rw [← mul_assoc]; exact Nat.choose_mul_factorial_mul_factorial (by omega)
  have e2 : Nat.choose (2*t) t * (t ! * ((2*t) - t)!) = (2*t)! := by
    rw [← mul_assoc]; exact Nat.choose_mul_factorial_mul_factorial (by omega)
  have h32 : (3*t) - t = 2*t := by omega
  have h22 : (2*t) - t = t := by omega
  rw [h32] at e1; rw [h22] at e2
  calc Nat.choose (3*t) t * Nat.choose (2*t) t * (t !)^3
      = Nat.choose (3*t) t * (t ! * (2*t)!) := by
        have : Nat.choose (2*t) t * (t ! * t !) = (2*t)! := e2
        calc Nat.choose (3*t) t * Nat.choose (2*t) t * (t !)^3
            = Nat.choose (3*t) t * (Nat.choose (2*t) t * (t ! * t !) * t !) := by ring
          _ = Nat.choose (3*t) t * ((2*t)! * t !) := by rw [this]
          _ = Nat.choose (3*t) t * (t ! * (2*t)!) := by ring
    _ = (3*t)! := e1

-- 4^t ≤ (2t+1) * C(2t,t).
/-- **Four-power lower bound for the central binomial coefficient.** For every natural number
$t$, $4^t \le (2t+1)\binom{2t}{t}$. -/
lemma four_pow_le (t : ℕ) : 4^t ≤ (2*t+1) * Nat.choose (2*t) t := by
  have hsum : (2:ℕ)^(2*t) = ∑ k ∈ Finset.range (2*t+1), Nat.choose (2*t) k :=
    (Nat.sum_range_choose (2*t)).symm
  have hle : ∑ k ∈ Finset.range (2*t+1), Nat.choose (2*t) k
      ≤ ∑ k ∈ Finset.range (2*t+1), Nat.choose (2*t) t := by
    apply Finset.sum_le_sum
    intro k _
    have := Nat.choose_le_middle k (2*t)
    rwa [show 2*t/2 = t by omega] at this
  have hcard : ∑ _k ∈ Finset.range (2*t+1), Nat.choose (2*t) t
      = (2*t+1) * Nat.choose (2*t) t := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_comm]
  have h4 : (4:ℕ)^t = 2^(2*t) := by rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul]
  omega

-- Key: 2*M(t) ≤ 432^t * (2t+1).
/-- **Key estimate for the multinomial coefficient $M(t)$.** Let
$M(t) = \frac{(6t)!}{(3t)!\,(2t)!\,t!}$. For every natural number $t \ge 1$,
$2\,M(t) \le 432^t \, (2t + 1)$. -/
lemma M34_key (t : ℕ) (ht : 1 ≤ t) : 2 * M34 t ≤ 432^t * (2*t+1) := by
  have hC : 0 < Nat.choose (2*t) t := Nat.choose_pos (by omega)
  have h1 : 2 * Nat.choose (6*t) (3*t) ≤ 2^(6*t) := by
    have h := choose_middle_half (show 1 ≤ 3*t by omega)
    have h6 : 2*(3*t) = 6*t := by ring
    rw [h6] at h
    have hpow : (2:ℕ)^(6*t) = 2 * 2^(6*t-1) := by
      conv_lhs => rw [show 6*t = (6*t-1)+1 by omega, pow_succ']
    omega
  have h2 : Nat.choose (3*t) t * Nat.choose (2*t) t ≤ 3^(3*t) := by
    have hmul := multinomial3_le t
    have heq := choose3_mul_choose2 t
    have hpos : 0 < (t !)^3 := by positivity
    have : Nat.choose (3*t) t * Nat.choose (2*t) t * (t !)^3 ≤ 3^(3*t) * (t !)^3 := by
      rw [heq]; exact hmul
    exact le_of_mul_le_mul_right this hpos
  have h3 : (2:ℕ)^(6*t) * 3^(3*t) = 432^t * 4^t := by
    have e1 : (2:ℕ)^(6*t) = 64^t := by rw [show (64:ℕ) = 2^6 by norm_num, ← pow_mul]
    have e2 : (3:ℕ)^(3*t) = 27^t := by rw [show (27:ℕ) = 3^3 by norm_num, ← pow_mul]
    rw [e1, e2, ← mul_pow, ← mul_pow]
    congr 1
  have h4 := four_pow_le t
  have hM := M34_eq_choose_mul t
  have hmain : 2 * M34 t * Nat.choose (2*t) t ≤ 432^t * (2*t+1) * Nat.choose (2*t) t := by
    calc 2 * M34 t * Nat.choose (2*t) t
        = (2 * Nat.choose (6*t) (3*t)) * (Nat.choose (3*t) t * Nat.choose (2*t) t) := by
          rw [hM]; ring
      _ ≤ 2^(6*t) * 3^(3*t) := Nat.mul_le_mul h1 h2
      _ = 432^t * 4^t := h3
      _ ≤ 432^t * ((2*t+1) * Nat.choose (2*t) t) := Nat.mul_le_mul_left _ h4
      _ = 432^t * (2*t+1) * Nat.choose (2*t) t := by ring
  exact le_of_mul_le_mul_right hmain hC

set_option exponentiation.threshold 300000 in
/-- **Base case of the threshold inequality.** The inequality
$10^{1145} \cdot 432^{230} \cdot 461 \le 2 \cdot 34^{1145}$ holds; this is the inequality
$10^{5t-5} \cdot 432^{t} \cdot (2t+1) \le 2 \cdot 34^{5t-5}$ at $t = 230$.

Checked by direct computation. -/
lemma P34_base : 10^(5*230-5) * 432^230 * (2*230+1) ≤ 2 * 34^(5*230-5) := by
  decide

-- Threshold inequality, induction step.
/-- **Induction step of the threshold inequality.** Let $t \ge 230$ be a natural number. If
$10^{5t-5} \cdot 432^{t} \cdot (2t+1) \le 2 \cdot 34^{5t-5}$, then
$10^{5t} \cdot 432^{t+1} \cdot (2t+3) \le 2 \cdot 34^{5t}$, which is the same inequality with
$t+1$ in place of $t$. -/
lemma P34_step (t : ℕ) (ht : 230 ≤ t)
    (ih : 10 ^ (5 * t - 5) * 432 ^ t * (2 * t + 1) ≤ 2 * 34 ^ (5 * t - 5)) :
    10 ^ (5 * (t + 1) - 5) * 432 ^ (t + 1) * (2 * (t + 1) + 1) ≤ 2 * 34 ^ (5 * (t + 1) - 5) := by
  have hpos : 0 < 2 * t + 1 := by omega
  have hkey' : 10 ^ 5 * 432 * (2 * t + 3) ≤ 34 ^ 5 * (2 * t + 1) := by
    rw [show (34 : ℕ) ^ 5 = 45435424 by norm_num, show (10 : ℕ) ^ 5 = 100000 by norm_num]
    omega
  have eL : 10 ^ (5 * (t + 1) - 5) * 432 ^ (t + 1) * (2 * (t + 1) + 1) * (2 * t + 1)
      = (10 ^ (5 * t - 5) * 432 ^ t * (2 * t + 1)) * (10 ^ 5 * 432 * (2 * t + 3)) := by
    rw [show 5 * (t + 1) - 5 = (5 * t - 5) + 5 by omega, show 2 * (t + 1) + 1 = 2 * t + 3 by omega,
      pow_add, pow_succ]
    ring
  have eR : 2 * 34 ^ (5 * (t + 1) - 5) * (2 * t + 1)
      = (2 * 34 ^ (5 * t - 5)) * (34 ^ 5 * (2 * t + 1)) := by
    rw [show 5 * (t + 1) - 5 = (5 * t - 5) + 5 by omega, pow_add]
    ring
  apply le_of_mul_le_mul_right _ hpos
  rw [eL, eR]
  exact Nat.mul_le_mul ih hkey'

/-- **Threshold inequality for the multinomial bound.** For every natural number $t \ge 230$,
$10^{5t-5} \cdot 432^{t} \cdot (2t+1) \le 2 \cdot 34^{5t-5}$. -/
lemma P34 (t : ℕ) (ht : 230 ≤ t) :
    10^(5*t-5) * 432^t * (2*t+1) ≤ 2 * 34^(5*t-5) := by
  induction t, ht using Nat.le_induction with
  | base => exact P34_base
  | succ t h ih => exact P34_step t h ih

/-- **Power bound for the multinomial coefficient $M(t)$, large $t$.** Let
$M(t) = \frac{(6t)!}{(3t)!\,(2t)!\,t!}$. For every natural number $t \ge 230$,
$10^{5t-5} \cdot M(t) \le 34^{5t-5}$, that is, $M(t) \le 3.4^{5t-5}$. -/
lemma M34_bound_large (t : ℕ) (ht : 230 ≤ t) : 10^(5*t-5) * M34 t ≤ 34^(5*t-5) := by
  have h1 : 1 ≤ t := by omega
  have hkey := M34_key t h1
  have hP := P34 t ht
  have h2 : 2 * (10^(5*t-5) * M34 t) ≤ 2 * 34^(5*t-5) := by
    calc 2 * (10^(5*t-5) * M34 t)
        = 10^(5*t-5) * (2 * M34 t) := by ring
      _ ≤ 10^(5*t-5) * (432^t * (2*t+1)) := by gcongr
      _ = 10^(5*t-5) * 432^t * (2*t+1) := by ring
      _ ≤ 2 * 34^(5*t-5) := hP
  omega

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 3200000 in
-- Direct evaluation covers the finite gap below the analytic threshold.
/-- **Power bound for the multinomial coefficient $M(t)$, small $t$.** Let
$M(t) = \frac{(6t)!}{(3t)!\,(2t)!\,t!}$. For every natural number $k < 207$, writing
$t = 23 + k$ (so $23 \le t < 230$), we have $10^{5t-5} \cdot M(t) \le 34^{5t-5}$.

The finitely many cases are checked by direct computation. -/
lemma M34_bound_small : ∀ k < 207,
    10 ^ (5 * (23 + k) - 5) * M34 (23 + k) ≤ 34 ^ (5 * (23 + k) - 5) := by
  decide

/-- **Power bound for the multinomial coefficient $M(t)$.** Let
$M(t) = \frac{(6t)!}{(3t)!\,(2t)!\,t!}$. For every natural number $t \ge 23$,
$10^{5t-5} \cdot M(t) \le 34^{5t-5}$, that is, $M(t) \le 3.4^{5t-5}$. -/
lemma M34_bound (t : ℕ) (ht : 23 ≤ t) : 10^(5*t-5) * M34 t ≤ 34^(5*t-5) := by
  by_cases ht230 : 230 ≤ t
  · exact M34_bound_large t ht230
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
    exact M34_bound_small k (by omega)

-- Sum of floors ≤ floor of sum (three terms).
/-- **Superadditivity of floor division for three terms.** For natural numbers $a, b, c$ and
$q > 0$, $\lfloor a/q \rfloor + \lfloor b/q \rfloor + \lfloor c/q \rfloor \le
\lfloor (a+b+c)/q \rfloor$. -/
lemma div_add_div_add_div_le (a b c q : ℕ) (hq : 0 < q) :
    a / q + b / q + c / q ≤ (a + b + c) / q := by
  rw [Nat.le_div_iff_mul_le hq]
  have h1 := Nat.div_mul_le_self a q
  have h2 := Nat.div_mul_le_self b q
  have h3 := Nat.div_mul_le_self c q
  calc (a / q + b / q + c / q) * q
      = (a/q)*q + (b/q)*q + (c/q)*q := by ring
    _ ≤ a + b + c := by omega

-- j=1 Legendre term ≥ 1 on (t, 6t]: five ranges.
/-- **Floor-difference bound on the range 3t < p ≤ 6t.** Let $t \ge 1$ and $p$ be natural
numbers with $3t < p \le 6t$. Then
$\lfloor 6t/p \rfloor - \lfloor 3t/p \rfloor - \lfloor 2t/p \rfloor \ge 1$. -/
lemma vp_term_case1 (t p : ℕ) (_ht : 1 ≤ t) (hlo : 3 * t < p) (hhi : p ≤ 6 * t) :
    1 ≤ 6 * t / p - 3 * t / p - 2 * t / p := by
  have h6 : 6 * t / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h3 : 3 * t / p = 0 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h2 : 2 * t / p = 0 := Nat.div_eq_of_lt_le (by omega) (by omega)
  omega

/-- **Floor-difference bound on the range 2t < p ≤ 3t.** Let $t \ge 1$ and $p$ be natural
numbers with $2t < p \le 3t$. Then
$\lfloor 6t/p \rfloor - \lfloor 3t/p \rfloor - \lfloor 2t/p \rfloor \ge 1$. -/
lemma vp_term_case2 (t p : ℕ) (_ht : 1 ≤ t) (hlo : 2 * t < p) (hhi : p ≤ 3 * t) :
    1 ≤ 6 * t / p - 3 * t / p - 2 * t / p := by
  have h6 : 6 * t / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h3 : 3 * t / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h2 : 2 * t / p = 0 := Nat.div_eq_of_lt_le (by omega) (by omega)
  omega

/-- **Floor-difference bound on the range 3t/2 < p ≤ 2t.** Let $t \ge 1$ and $p$ be natural
numbers with $3t < 2p$ and $p \le 2t$. Then
$\lfloor 6t/p \rfloor - \lfloor 3t/p \rfloor - \lfloor 2t/p \rfloor \ge 1$. -/
lemma vp_term_case3 (t p : ℕ) (_ht : 1 ≤ t) (hlo : 3 * t < 2 * p) (hhi : p ≤ 2 * t) :
    1 ≤ 6 * t / p - 3 * t / p - 2 * t / p := by
  have h6 : 6 * t / p = 3 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h3 : 3 * t / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h2 : 2 * t / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  omega

/-- **Floor-difference bound on the range 6t/5 < p ≤ 3t/2.** Let $t \ge 1$ and $p$ be natural
numbers with $6t < 5p$ and $2p \le 3t$. Then
$\lfloor 6t/p \rfloor - \lfloor 3t/p \rfloor - \lfloor 2t/p \rfloor \ge 1$. -/
lemma vp_term_case4 (t p : ℕ) (ht : 1 ≤ t) (hlo : 6 * t < 5 * p) (hhi : 2 * p ≤ 3 * t) :
    1 ≤ 6 * t / p - 3 * t / p - 2 * t / p := by
  have h6 : 6 * t / p = 4 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h3 : 3 * t / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h2 : 2 * t / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  omega

/-- **Floor-difference bound on the range t < p ≤ 6t/5.** Let $t \ge 1$ and $p$ be natural
numbers with $t < p$ and $5p \le 6t$. Then
$\lfloor 6t/p \rfloor - \lfloor 3t/p \rfloor - \lfloor 2t/p \rfloor \ge 1$. -/
lemma vp_term_case5 (t p : ℕ) (_ht : 1 ≤ t) (hlo : t < p) (hhi : 5 * p ≤ 6 * t) :
    1 ≤ 6 * t / p - 3 * t / p - 2 * t / p := by
  have h6 : 6 * t / p = 5 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h3 : 3 * t / p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have h2 : 2 * t / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
  omega

/-- **Floor-difference bound on the range t < p ≤ 6t.** Let $t \ge 1$ and $p$ be natural
numbers with $t < p \le 6t$. Then
$\lfloor 6t/p \rfloor - \lfloor 3t/p \rfloor - \lfloor 2t/p \rfloor \ge 1$.

This is the $j = 1$ term of Legendre's formula for the exponent of $p$ in
$(6t)!/((3t)!\,(2t)!\,t!)$; on this range $\lfloor t/p \rfloor = 0$. -/
lemma vp_term1 (t p : ℕ) (ht : 1 ≤ t) (hlo : t < p) (hhi : p ≤ 6 * t) :
    1 ≤ 6 * t / p - 3 * t / p - 2 * t / p := by
  by_cases h1 : 3 * t < p
  · exact vp_term_case1 t p ht h1 hhi
  · by_cases h2 : 2 * t < p
    · exact vp_term_case2 t p ht h2 (by omega)
    · by_cases h3 : 3 * t < 2 * p
      · exact vp_term_case3 t p ht h3 (by omega)
      · by_cases h4 : 6 * t < 5 * p
        · exact vp_term_case4 t p ht h4 (by omega)
        · exact vp_term_case5 t p ht hlo (by omega)

-- Every prime in (t, 6t] divides M(t).
/-- **Primes in $(t, 6t]$ occur in $M(t)$.** For every natural number $t \ge 1$ and every prime $p$
with $t < p \le 6t$, the exponent of $p$ in the prime factorization of the multinomial coefficient
$M(t) = (6t)!/((3t)!\,(2t)!\,t!)$ is at least $1$. -/
lemma vp_M34 (t : ℕ) (ht : 1 ≤ t) (p : ℕ) (hp : p.Prime)
    (hlo : t < p) (hhi : p ≤ 6 * t) : 1 ≤ (M34 t).factorization p := by
  set B : ℕ := Nat.log p (6 * t) + 2 with hB
  have hB6 : Nat.log p (6 * t) < B := by omega
  have hB3 : Nat.log p (3 * t) < B :=
    lt_of_le_of_lt (Nat.log_mono_right (by omega)) hB6
  have hB2 : Nat.log p (2 * t) < B :=
    lt_of_le_of_lt (Nat.log_mono_right (by omega)) hB6
  have hBt : Nat.log p t < B :=
    lt_of_le_of_lt (Nat.log_mono_right (by omega)) hB6
  have e6 := Nat.factorization_factorial hp hB6
  have e3 := Nat.factorization_factorial hp hB3
  have e2 := Nat.factorization_factorial hp hB2
  have et := Nat.factorization_factorial hp hBt
  have hsum6 : (((6 * t)!).factorization p : ℤ)
      = ∑ j ∈ Finset.Ico 1 B, ((6 * t / p ^ j : ℕ) : ℤ) := by exact_mod_cast e6
  have hsum3 : (((3 * t)!).factorization p : ℤ)
      = ∑ j ∈ Finset.Ico 1 B, ((3 * t / p ^ j : ℕ) : ℤ) := by exact_mod_cast e3
  have hsum2 : (((2 * t)!).factorization p : ℤ)
      = ∑ j ∈ Finset.Ico 1 B, ((2 * t / p ^ j : ℕ) : ℤ) := by exact_mod_cast e2
  have hsumt : (((t !)).factorization p : ℤ)
      = ∑ j ∈ Finset.Ico 1 B, ((t / p ^ j : ℕ) : ℤ) := by exact_mod_cast et
  have hMnat : (M34 t).factorization p
      + (((3 * t)!).factorization p + ((2 * t)!).factorization p + (t !).factorization p)
      = ((6 * t)!).factorization p := by
    have hmul : ((M34 t * ((3 * t)! * (2 * t)! * t !))).factorization p
        = (M34 t).factorization p + (((3 * t)! * (2 * t)! * t !)).factorization p := by
      rw [Nat.factorization_mul (ne_of_gt (M34_pos t))
        (show (3 * t)! * (2 * t)! * t ! ≠ 0 by positivity), Finsupp.add_apply]
    rw [M34_eq_mul] at hmul
    have hX : (((3 * t)! * (2 * t)! * t !)).factorization p
        = ((3 * t)!).factorization p + ((2 * t)!).factorization p + (t !).factorization p := by
      rw [Nat.factorization_mul (show (3 * t)! * (2 * t)! ≠ 0 by positivity)
          (show t ! ≠ 0 by positivity), Finsupp.add_apply,
        Nat.factorization_mul (show (3 * t)! ≠ 0 by positivity)
          (show (2 * t)! ≠ 0 by positivity), Finsupp.add_apply]
    omega
  have hsub : ∑ j ∈ Finset.Ico 1 B, (((6 * t / p ^ j : ℕ) : ℤ))
      - ∑ j ∈ Finset.Ico 1 B, (((3 * t / p ^ j : ℕ) : ℤ))
      - ∑ j ∈ Finset.Ico 1 B, (((2 * t / p ^ j : ℕ) : ℤ))
      - ∑ j ∈ Finset.Ico 1 B, (((t / p ^ j : ℕ) : ℤ))
      = ∑ j ∈ Finset.Ico 1 B, ((((6 * t / p ^ j : ℕ) : ℤ) - ((3 * t / p ^ j : ℕ) : ℤ)
        - ((2 * t / p ^ j : ℕ) : ℤ) - ((t / p ^ j : ℕ) : ℤ))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  have hM : ((M34 t).factorization p : ℤ)
      = ∑ j ∈ Finset.Ico 1 B, ((((6 * t / p ^ j : ℕ) : ℤ) - ((3 * t / p ^ j : ℕ) : ℤ)
        - ((2 * t / p ^ j : ℕ) : ℤ) - ((t / p ^ j : ℕ) : ℤ))) := by
    have hZ : ((M34 t).factorization p : ℤ)
        + ((((3 * t)!).factorization p : ℤ) + (((2 * t)!).factorization p : ℤ)
          + ((t !).factorization p : ℤ))
        = (((6 * t)!).factorization p : ℤ) := by exact_mod_cast hMnat
    rw [hsum6, hsum3, hsum2, hsumt] at hZ
    have hM2 : ((M34 t).factorization p : ℤ)
        = ∑ j ∈ Finset.Ico 1 B, (((6 * t / p ^ j : ℕ) : ℤ))
        - ∑ j ∈ Finset.Ico 1 B, (((3 * t / p ^ j : ℕ) : ℤ))
        - ∑ j ∈ Finset.Ico 1 B, (((2 * t / p ^ j : ℕ) : ℤ))
        - ∑ j ∈ Finset.Ico 1 B, (((t / p ^ j : ℕ) : ℤ)) := by linarith
    rw [hM2, hsub]
  have hnn : ∀ j ∈ Finset.Ico 1 B, (0 : ℤ) ≤ ((((6 * t / p ^ j : ℕ) : ℤ)
      - ((3 * t / p ^ j : ℕ) : ℤ) - ((2 * t / p ^ j : ℕ) : ℤ) - ((t / p ^ j : ℕ) : ℤ))) := by
    intro j _
    have hq : 0 < p ^ j := pow_pos hp.pos j
    have hle := div_add_div_add_div_le (3 * t) (2 * t) t (p ^ j) hq
    have heq : 3 * t + 2 * t + t = 6 * t := by ring
    rw [heq] at hle
    have hZ2 : ((3 * t / p ^ j + 2 * t / p ^ j + t / p ^ j : ℕ) : ℤ) ≤ ((6 * t / p ^ j : ℕ) : ℤ) :=
      by exact_mod_cast hle
    rw [Nat.cast_add, Nat.cast_add] at hZ2
    linarith
  have h1mem : 1 ∈ Finset.Ico 1 B := by simp only [Finset.mem_Ico]; omega
  have hterm1 : (1 : ℤ) ≤ ((((6 * t / p ^ 1 : ℕ) : ℤ) - ((3 * t / p ^ 1 : ℕ) : ℤ)
      - ((2 * t / p ^ 1 : ℕ) : ℤ) - ((t / p ^ 1 : ℕ) : ℤ))) := by
    rw [pow_one]
    have ht1 := vp_term1 t p ht hlo hhi
    have hnat : 3 * t / p + 2 * t / p + 1 ≤ 6 * t / p := by omega
    have hZ3 : ((3 * t / p : ℕ):ℤ) + ((2 * t / p : ℕ):ℤ) + 1 ≤ ((6 * t / p : ℕ):ℤ) := by
      exact_mod_cast hnat
    have htp : t / p = 0 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have htpZ : ((t / p : ℕ):ℤ) = 0 := by exact_mod_cast htp
    linarith
  have hsingle := Finset.single_le_sum hnn h1mem
  have hfin : (1 : ℤ) ≤ ((M34 t).factorization p : ℤ) := by
    rw [hM]
    exact le_trans hterm1 hsingle
  exact_mod_cast hfin

-- Θ(m) ≤ Θ(t) * M(t) for t = (m+5)/6.
/-- **Splitting the primorial with a multinomial coefficient.** For a natural number $n$ let
$n\#$ be the primorial, the product of the primes $p \le n$, and let
$M(t) = \frac{(6t)!}{(3t)!\,(2t)!\,t!}$. For every natural number $m \ge 1$, with
$t = \lfloor (m+5)/6 \rfloor$, we have $m\# \le t\# \cdot M(t)$. -/
lemma theta_le_M34 (m : ℕ) (hm : 1 ≤ m) :
    primorial m ≤ primorial ((m+5)/6) * M34 ((m+5)/6) := by
  set t : ℕ := (m+5)/6 with ht
  have ht1 : 1 ≤ t := by omega
  have htm : t ≤ m := by omega
  have hm6 : m ≤ 6*t := by omega
  have hsplit : primorial m
      = primorial t * ∏ p ∈ Finset.Ico (t+1) (m+1) with p.Prime, p := by
    have h := primorial_add t (m - t)
    rw [show t + (m - t) = m by omega] at h
    exact h
  have hdvd : ∏ p ∈ Finset.Ico (t+1) (m+1) with p.Prime, p ∣ M34 t := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Finset.mem_filter.mp hp).2.prime
    · intro p hp
      rw [Finset.mem_filter, Finset.mem_Ico] at hp
      have hplo : t < p := by omega
      have hphi : p ≤ 6*t := by omega
      have hvp := vp_M34 t ht1 p hp.2 hplo hphi
      have hord := Nat.ordProj_dvd (M34 t) p
      have hpow : p^1 ∣ M34 t := dvd_trans (pow_dvd_pow p hvp) hord
      rwa [pow_one] at hpow
  rw [hsplit]
  have hle : ∏ p ∈ Finset.Ico (t+1) (m+1) with p.Prime, p ≤ M34 t :=
    Nat.le_of_dvd (M34_pos t) hdvd
  exact mul_le_mul_of_nonneg_left hle (Nat.zero_le _)

/-- **Primorial bound $3.4^m$ below $133$.** For a natural number $n$ let $n\#$ be the
primorial, the product of the primes $p \le n$. For every natural number $m < 133$,
$10^m \cdot m\# \le 34^m$.

Proved by covering $0 \le m \le 132$ with finitely many intervals $[a, b]$ and checking
$10^a \cdot b\# \le 34^a$ for each; this gives the bound on $[a, b]$ because $n\#$ is
nondecreasing in $n$ and $10 \le 34$. -/
lemma theta34_base : ∀ m : ℕ, m < 133 → 10^m * primorial m ≤ 34^m := by
  intro m hm
  by_cases h1 : m ≤ 1
  · exact theta34_of_interval (Nat.zero_le m) h1 theta34_at_1
  by_cases h4 : m ≤ 4
  · exact theta34_of_interval (by omega) h4 theta34_at_4
  by_cases h10 : m ≤ 10
  · exact theta34_of_interval (by omega) h10 theta34_at_10
  by_cases h18 : m ≤ 18
  · exact theta34_of_interval (by omega) h18 theta34_at_18
  by_cases h30 : m ≤ 30
  · exact theta34_of_interval (by omega) h30 theta34_at_30
  by_cases h46 : m ≤ 46
  · exact theta34_of_interval (by omega) h46 theta34_at_46
  by_cases h70 : m ≤ 70
  · exact theta34_of_interval (by omega) h70 theta34_at_70
  by_cases h100 : m ≤ 100
  · exact theta34_of_interval (by omega) h100 theta34_at_100
  exact theta34_of_interval (by omega) (by omega) theta34_at_132

-- Θ(m) ≤ 3.4^m for all m, in integer form.
/-- **Primorial bound by powers of 3.4, integer form.** For every natural number $m$, the
primorial $m\#$ (the product of all primes $p \le m$) satisfies $10^m \cdot m\# \le 34^m$. -/
lemma theta34_nat (m : ℕ) : 10^m * primorial m ≤ 34^m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm : m < 133
    · exact theta34_base m hm
    · set t : ℕ := (m+5)/6 with ht
      have hm1 : 1 ≤ m := by omega
      have htm : t < m := by omega
      have ht23 : 23 ≤ t := by omega
      have h6t : 6*t ≤ m+5 := by
        have h := Nat.div_mul_le_self (m+5) 6
        rw [ht]
        calc 6*((m+5)/6) = ((m+5)/6)*6 := by ring
          _ ≤ m+5 := h
      have hle := theta_le_M34 m hm1
      have hIH := ih t htm
      have hM := M34_bound t ht23
      have hgap : 5*t-5 ≤ m-t := by omega
      have h10M : 10^(m-t) * M34 t ≤ 34^(m-t) := by
        have e1 : m - t = (5*t-5) + (m-t-(5*t-5)) := by omega
        rw [e1, pow_add, pow_add]
        have h10 : (10:ℕ)^(m-t-(5*t-5)) ≤ 34^(m-t-(5*t-5)) :=
          Nat.pow_le_pow_left (by norm_num) _
        calc 10^(5*t-5) * 10^(m-t-(5*t-5)) * M34 t
            = (10^(5*t-5) * M34 t) * 10^(m-t-(5*t-5)) := by ring
          _ ≤ 34^(5*t-5) * 34^(m-t-(5*t-5)) := Nat.mul_le_mul hM h10
      have e2 : m = t + (m-t) := by omega
      calc 10^m * primorial m
          = (10^t * 10^(m-t)) * primorial m := by
            have hexp : (10:ℕ)^m = 10^t * 10^(m-t) := by
              conv_lhs => rw [show m = t + (m - t) by omega]
              rw [pow_add]
            rw [hexp]
        _ ≤ (10^t * 10^(m-t)) * (primorial t * M34 t) := by
            apply mul_le_mul_of_nonneg_left hle (by positivity)
        _ = (10^t * primorial t) * (10^(m-t) * M34 t) := by ring
        _ ≤ 34^t * 34^(m-t) := Nat.mul_le_mul hIH h10M
        _ = 34^m := by rw [← pow_add, show t + (m - t) = m by omega]

-- Θ(x) ≤ 3.4^x for real x ≥ 0.
/-- **Primorial bound by powers of 3.4, real form.** For every real number $x \ge 0$, the
primorial of $\lfloor x \rfloor$ (the product of all primes $p \le \lfloor x \rfloor$) is at
most $3.4^x$, where $3.4^x$ is the real power. -/
lemma theta34_real {x : ℝ} (hx : 0 ≤ x) :
    (primorial ⌊x⌋₊ : ℝ) ≤ (3.4 : ℝ)^x := by
  have hnat := theta34_nat ⌊x⌋₊
  have hR : (10:ℝ)^((⌊x⌋₊ : ℕ)) * (primorial ⌊x⌋₊ : ℝ) ≤ (34:ℝ)^((⌊x⌋₊ : ℕ)) := by
    exact_mod_cast hnat
  have h10 : (0:ℝ) < (10:ℝ)^((⌊x⌋₊ : ℕ)) := by positivity
  have hcast : (primorial ⌊x⌋₊ : ℝ) ≤ ((34:ℝ)/10)^((⌊x⌋₊ : ℕ)) := by
    rw [div_pow]
    rw [le_div_iff₀ h10]
    linarith [hR]
  have h34 : ((34:ℝ)/10) = 3.4 := by norm_num
  rw [h34] at hcast
  have hle : ((⌊x⌋₊ : ℕ):ℝ) ≤ x := Nat.floor_le hx
  calc (primorial ⌊x⌋₊ : ℝ) ≤ (3.4:ℝ)^((⌊x⌋₊ : ℕ)) := hcast
    _ = (3.4:ℝ)^(((⌊x⌋₊ : ℕ):ℝ)) := (Real.rpow_natCast _ _).symm
    _ ≤ (3.4:ℝ)^x := Real.rpow_le_rpow_of_exponent_le (by norm_num) hle

/-- **Bounding a logarithm above by the exponential.** Let $a$ and $r$ be real numbers with
$a > 0$. If $a < e^r$, then $\log a < r$, where $\log$ is the natural logarithm. -/
lemma log_lt_of_exp_gt {a r : ℝ} (ha : 0 < a) (h : a < Real.exp r) :
    Real.log a < r := by
  have h2 := (Real.log_lt_log_iff ha (Real.exp_pos r)).mpr h
  rwa [Real.log_exp] at h2

/-- **Logarithm lower bound from an exponential bound.** For real numbers $a > 0$ and $r$, if
$e^r < a$ then $r < \log a$, where $\log$ is the natural logarithm. -/
lemma log_gt_of_exp_lt {a r : ℝ} (ha : 0 < a) (h : Real.exp r < a) :
    r < Real.log a := by
  have h2 := (Real.log_lt_log_iff (Real.exp_pos r) ha).mpr h
  rwa [Real.log_exp] at h2

-- If a^n < c^m with c < e, then a < e^{m/n}.
/-- **Exponential lower bound from a power comparison.** Let $a$ and $c$ be nonnegative real
numbers and let $n$ and $m$ be positive integers. If $c < e$ and $a^n < c^m$, then
$a < e^{m/n}$, where $m/n$ is real division. -/
lemma lt_exp_of_pow_lt {a c : ℝ} {n m : ℕ} (ha : 0 ≤ a) (hn : n ≠ 0) (hm : m ≠ 0)
    (hc : c < Real.exp 1) (hc0 : 0 ≤ c) (h : a ^ n < c ^ m) :
    a < Real.exp ((m : ℝ) / n) := by
  have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have e1 : (Real.exp ((m : ℝ) / n)) ^ n = Real.exp (m : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have e2 : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hpow : c ^ m < (Real.exp 1) ^ m :=
    pow_lt_pow_left₀ hc hc0 hm
  have h1 : a ^ n < (Real.exp ((m : ℝ) / n)) ^ n := by
    rw [e1, e2]
    linarith
  exact (pow_lt_pow_iff_left₀ ha (le_of_lt (Real.exp_pos _)) hn).mp h1

-- If c^m < a^n with e < c, then e^{m/n} < a.
/-- **Power comparison above e bounds an exponential.** Let $e$ be Euler's number, let $a$
and $c$ be real numbers and let $m, n$ be nonzero natural numbers, with $a \ge 0$,
$e^{m/n} \ge 0$ and $c > e$. If $c^m < a^n$, then $e^{m/n} < a$. -/
lemma exp_lt_of_pow_lt {a c : ℝ} {n m : ℕ} (ha : 0 ≤ a) (hn : n ≠ 0) (hm : m ≠ 0)
    (hc : Real.exp 1 < c) (ha0 : 0 ≤ Real.exp ((m : ℝ) / n)) (h : c ^ m < a ^ n) :
    Real.exp ((m : ℝ) / n) < a := by
  have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have e1 : (Real.exp ((m : ℝ) / n)) ^ n = Real.exp (m : ℝ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  have e2 : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hpow : (Real.exp 1) ^ m < c ^ m :=
    pow_lt_pow_left₀ hc (le_of_lt (Real.exp_pos 1)) hm
  have h1 : (Real.exp ((m : ℝ) / n)) ^ n < a ^ n := by
    rw [e1, e2]
    linarith
  exact (pow_lt_pow_iff_left₀ ha0 ha hn).mp h1

/-- **Lower bound for log 2.** The natural logarithm of $2$ satisfies $0.6931 < \log 2$. -/
lemma log2_gt : (0.6931 : ℝ) < Real.log 2 := by
  have hnat : 27182818286 ^ 6931 < 2 ^ 10000 * 10 ^ 69310 := by
    set_option exponentiation.threshold 300000 in
    decide
  have hcore : (2.7182818286 : ℝ) ^ 6931 < (2 : ℝ) ^ 10000 := by
    rw [show (2.7182818286 : ℝ) = 27182818286 / 10 ^ 10 by norm_num, div_pow]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ((10 : ℝ) ^ 10) ^ 6931)]
    have h10 : (((10 : ℝ) ^ 10) ^ 6931) = (10 : ℝ) ^ 69310 := by
      rw [← pow_mul]
    rw [h10]
    exact_mod_cast hnat
  have h : Real.exp ((6931 : ℝ) / 10000) < (2 : ℝ) :=
    exp_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
      Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) hcore
  have heq : ((6931 : ℝ) / 10000) = 0.6931 := by norm_num
  rw [heq] at h
  exact log_gt_of_exp_lt (by norm_num) h

/-- **Lower bound for log 5.** The natural logarithm of $5$ satisfies $1.6094 < \log 5$. -/
lemma log5_gt : (1.6094 : ℝ) < Real.log 5 := by
  have hnat : 27182818286 ^ 16094 < 5 ^ 10000 * 10 ^ 160940 := by
    set_option exponentiation.threshold 300000 in
    decide
  have hcore : (2.7182818286 : ℝ) ^ 16094 < (5 : ℝ) ^ 10000 := by
    rw [show (2.7182818286 : ℝ) = 27182818286 / 10 ^ 10 by norm_num, div_pow]
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ((10 : ℝ) ^ 10) ^ 16094)]
    have h10 : (((10 : ℝ) ^ 10) ^ 16094) = (10 : ℝ) ^ 160940 := by
      rw [← pow_mul]
    rw [h10]
    exact_mod_cast hnat
  have h : Real.exp ((16094 : ℝ) / 10000) < (5 : ℝ) :=
    exp_lt_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
      Real.exp_one_lt_d9 (le_of_lt (Real.exp_pos _)) hcore
  have heq : ((16094 : ℝ) / 10000) = 1.6094 := by norm_num
  rw [heq] at h
  exact log_gt_of_exp_lt (by norm_num) h

/-- **Upper bound for log 3.** The natural logarithm of $3$ satisfies $\log 3 < 1.0987$. -/
lemma log3_lt : Real.log 3 < (1.0987 : ℝ) := by
  have hnat : 3 ^ 10000 * 10 ^ 109870 < 27182818283 ^ 10987 := by
    set_option exponentiation.threshold 300000 in
    decide
  have hcore : (3 : ℝ) ^ 10000 < (2.7182818283 : ℝ) ^ 10987 := by
    rw [show (2.7182818283 : ℝ) = 27182818283 / 10 ^ 10 by norm_num, div_pow]
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < ((10 : ℝ) ^ 10) ^ 10987)]
    have h10 : (((10 : ℝ) ^ 10) ^ 10987) = (10 : ℝ) ^ 109870 := by
      rw [← pow_mul]
    rw [h10]
    exact_mod_cast hnat
  have h : (3 : ℝ) < Real.exp ((10987 : ℝ) / 10000) :=
    lt_exp_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
      Real.exp_one_gt_d9 (by norm_num) hcore
  have heq : ((10987 : ℝ) / 10000) = 1.0987 := by norm_num
  rw [heq] at h
  exact log_lt_of_exp_gt (by norm_num) h

/-- **Upper bound for log 17.** The natural logarithm of $17$ satisfies $\log 17 < 2.8333$. -/
lemma log17_lt : Real.log 17 < (2.8333 : ℝ) := by
  have hnat : 17 ^ 10000 * 10 ^ 283330 < 27182818283 ^ 28333 := by
    set_option exponentiation.threshold 300000 in
    decide
  have hcore : (17 : ℝ) ^ 10000 < (2.7182818283 : ℝ) ^ 28333 := by
    rw [show (2.7182818283 : ℝ) = 27182818283 / 10 ^ 10 by norm_num, div_pow]
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < ((10 : ℝ) ^ 10) ^ 28333)]
    have h10 : (((10 : ℝ) ^ 10) ^ 28333) = (10 : ℝ) ^ 283330 := by
      rw [← pow_mul]
    rw [h10]
    exact_mod_cast hnat
  have h : (17 : ℝ) < Real.exp ((28333 : ℝ) / 10000) :=
    lt_exp_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
      Real.exp_one_gt_d9 (by norm_num) hcore
  have heq : ((28333 : ℝ) / 10000) = 2.8333 := by norm_num
  rw [heq] at h
  exact log_lt_of_exp_gt (by norm_num) h

/-- **Logarithm of 10.** The natural logarithm satisfies $\log 10 = \log 2 + \log 5$. -/
lemma log10_eq : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
  rw [show (10 : ℝ) = 2 * 5 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]

/-- **Logarithm of 9.** The natural logarithm satisfies $\log 9 = 2 \log 3$. -/
lemma log9_eq : Real.log (9 : ℝ) = 2 * Real.log 3 := by
  rw [show (9 : ℝ) = (3 : ℝ) ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- **Logarithm of 3.4.** The natural logarithm satisfies $\log(34/10) = \log 17 - \log 5$. -/
lemma log34div10_eq : Real.log (34 / 10 : ℝ) = Real.log 17 - Real.log 5 := by
  rw [show (34 / 10 : ℝ) = 17 / 5 by norm_num,
    Real.log_div (by norm_num) (by norm_num)]

-- c9 as a single reduced rational (verified by norm_num below).
/-- **Evaluation of a three-term rational sum.** In the real numbers,
$\frac{18900}{279} + \frac{18900}{657} + \frac{18900}{963} = \frac{28121100}{242141}$.

The right-hand side is the sum written in lowest terms. -/
lemma c9_eq : (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) = 28121100 / 242141 := by
  norm_num

-- Verified margin: the gap LHS - RHS exceeds 13 (true gap ≈ 13.79).
/-- **Numerical margin of the main term.** With $\log$ the natural logarithm,
$48\,(10 \log 10 - 9 \log 9) -
\left(\frac{18900}{279} + \frac{18900}{657} + \frac{18900}{963}\right) \log \frac{34}{10} > 13$. -/
theorem T03c_eqmain_margin : 48 * (10 * Real.log 10 - 9 * Real.log 9) -
    (18900 / 279 + 18900 / 657 + 18900 / 963 : ℝ) * Real.log (34 / 10) > 13 := by
  rw [log10_eq, log9_eq, log34div10_eq, c9_eq]
  have l2 := log2_gt
  have l5 := log5_gt
  have l3 := log3_lt
  have l17 := log17_lt
  linarith

set_option maxRecDepth 16384 in
/-- **Prime-counting bound $\pi(m) \le m/3$ for $36 \le m < 156$.** Let $\pi(m)$ denote the
number of primes $p \le m$. For every natural number $m$ with $36 \le m < 156$, $3\pi(m) \le m$.

Checked by computation. -/
lemma pi_third_small : ∀ m : ℕ, 36 ≤ m → m < 156 → 3 * Nat.primeCounting m ≤ m := by
  decide

/-- **Prime-counting bound $\pi(m) \le m/3$ from $156$ on.** Let $\pi(m)$ denote the number of
primes $p \le m$. For every natural number $m \ge 156$, $3\pi(m) \le m$. -/
lemma pi_third_large (m : ℕ) (hm : 156 ≤ m) : 3 * Nat.primeCounting m ≤ m := by
  have h30 : (30 : ℕ) ≠ 0 := by norm_num
  have hle : (30 : ℕ) ≤ 36 := by norm_num
  have hbound := Nat.primeCounting_add_le h30 hle (m - 36)
  have hpi36 : Nat.primeCounting 36 = 11 := by decide
  have htot : Nat.totient 30 = 8 := by decide
  have hm36 : 36 + (m - 36) = m := by omega
  rw [hm36] at hbound
  rw [hpi36, htot] at hbound
  have hdiv := Nat.div_add_mod (m - 36) 30
  have hmod := Nat.mod_lt (m - 36) (by norm_num : 0 < 30)
  omega

/-- **Prime-counting bound $\pi(m) \le m/3$ for natural $m \ge 36$.** Let $\pi(m)$ denote the
number of primes $p \le m$. For every natural number $m \ge 36$, $3\pi(m) \le m$. -/
lemma pi_third_nat (m : ℕ) (hm36 : 36 ≤ m) : 3 * Nat.primeCounting m ≤ m := by
  by_cases hm : 156 ≤ m
  · exact pi_third_large m hm
  · push Not at hm
    exact pi_third_small m hm36 hm

/-- **Prime-counting bound $\pi(x) \le x/3$ for real $x \ge 36$.** Let $\pi(n)$ denote the
number of primes $p \le n$. For every real number $x \ge 36$, $\pi(\lfloor x \rfloor) \le x/3$. -/
theorem pi_third {x : ℝ} (hx : 36 ≤ x) : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / 3 := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hfloor : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  have hm36 : 36 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
  have h := pi_third_nat _ hm36
  have hcast : ((3 * Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) ≤ ((⌊x⌋₊ : ℕ) : ℝ) :=
    Nat.cast_le.mpr h
  push_cast at hcast
  linarith

-- Certified bound `log 10 < 2.4` via `10 ^ 5 < 2.7182818283 ^ 12`.
/-- **Upper bound for log 10.** The natural logarithm of $10$ satisfies $\log 10 < 2.4$. -/
lemma log10_lt : Real.log 10 < (2.4 : ℝ) := by
  have hnat : (10:ℕ)^125 < 27182818283^12 := by decide
  have hcore : (10:ℝ)^5 < (2.7182818283:ℝ)^12 := by
    rw [show (2.7182818283:ℝ) = 27182818283/10^10 by norm_num, div_pow]
    rw [lt_div_iff₀ (by positivity : (0:ℝ) < ((10:ℝ)^10)^12)]
    have h10 : (((10:ℝ)^10)^12) = (10:ℝ)^120 := by rw [← pow_mul]
    rw [h10]
    have h125 : (10:ℝ)^5*(10:ℝ)^120 = (10:ℝ)^125 := by ring
    rw [h125]
    exact_mod_cast hnat
  have h : (10:ℝ) < Real.exp ((12:ℝ)/5) :=
    lt_exp_of_pow_lt (by norm_num) (by norm_num) (by norm_num)
      Real.exp_one_gt_d9 (by norm_num) hcore
  have heq : ((12:ℝ)/5) = 2.4 := by norm_num
  rw [heq] at h
  exact log_lt_of_exp_gt (by norm_num) h

-- log x / √x is strictly decaying past e^2: for t > 1, the claim reduces to
-- log t < log a * (√t - 1), which follows from log a > 2 and log √t < √t - 1.
/-- **Strict decay of log over square root beyond e squared.** Let $a$ and $t$ be real numbers
with $a > 0$, $t > 1$ and $\log a > 2$, where $\log$ is the natural logarithm. Then
$\frac{\log(at)}{\sqrt{at}} < \frac{\log a}{\sqrt{a}}$. -/
lemma log_div_sqrt_decay {a t : ℝ} (ha : 0 < a) (ht : 1 < t)
    (hla : 2 < Real.log a) :
    Real.log (a*t) / Real.sqrt (a*t) < Real.log a / Real.sqrt a := by
  have ht0 : 0 < t := by linarith
  have hsq : Real.sqrt (a*t) = Real.sqrt a * Real.sqrt t :=
    Real.sqrt_mul (le_of_lt ha) t
  rw [hsq, Real.log_mul (ne_of_gt ha) (ne_of_gt ht0)]
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hst : 1 < Real.sqrt t := by
    have htsq : (Real.sqrt t)^2 = t := Real.sq_sqrt (le_of_lt ht0)
    nlinarith [Real.sqrt_nonneg t, ht, htsq, sq_nonneg (Real.sqrt t)]
  have hlogt : Real.log t < 2 * (Real.sqrt t - 1) := by
    have h1 : Real.log (Real.sqrt t) < Real.sqrt t - 1 :=
      Real.log_lt_sub_one_of_pos (Real.sqrt_pos.mpr ht0) (ne_of_gt hst)
    have h2 : Real.log t = 2 * Real.log (Real.sqrt t) := by
      nth_rewrite 1 [← Real.sq_sqrt (le_of_lt ht0)]
      rw [Real.log_pow]
      ring
    linarith
  have hkey : Real.log t < Real.log a * (Real.sqrt t - 1) := by
    have hpos : (0:ℝ) < (Real.log a - 2) * (Real.sqrt t - 1) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [hlogt, hpos]
  have hY : (0:ℝ) < Real.sqrt a * Real.sqrt t :=
    mul_pos hsa (Real.sqrt_pos.mpr ht0)
  rw [div_lt_iff₀ hY,
    show (Real.log a/Real.sqrt a)*(Real.sqrt a*Real.sqrt t)
      = (Real.log a*(Real.sqrt a*Real.sqrt t))/Real.sqrt a by ring,
    lt_div_iff₀ hsa]
  calc (Real.log a + Real.log t) * Real.sqrt a
      < (Real.log a + Real.log a * (Real.sqrt t - 1)) * Real.sqrt a := by
        apply mul_lt_mul_of_pos_right _ hsa
        linarith [hkey]
    _ = Real.log a * (Real.sqrt a * Real.sqrt t) := by ring

-- Main log-vs-sqrt bound.
/-- **Logarithm bounded by a multiple of the square root.** For every real number $x \ge 10^7$,
$\log x \le 0.006\sqrt{x}$, where $\log$ is the natural logarithm. -/
lemma log_le_sqrt06 (x : ℝ) (hx : (10 ^ 7 : ℝ) ≤ x) :
    Real.log x ≤ 0.006 * Real.sqrt x := by
  have hlog10 : (2.3025 : ℝ) < Real.log 10 := by
    have h2 := log2_gt
    have h5 := log5_gt
    have heq := log10_eq
    linarith
  have hla7 : (2 : ℝ) < Real.log (10 ^ 7 : ℝ) := by
    rw [show (10 ^ 7 : ℝ) = (10 : ℝ)^7 by norm_num, Real.log_pow]
    have h7 := mul_lt_mul_of_pos_left hlog10 (show (0 : ℝ) < 7 by norm_num)
    norm_num at h7 ⊢
    linarith
  have h10 : (1 : ℝ) ≤ x / 10 ^ 7 := by
    rw [le_div_iff₀ (by norm_num)]
    linarith
  set t := x / 10 ^ 7 with ht
  have hxeq : x = 10 ^ 7 * t := by rw [ht]; field_simp
  have hM : Real.log x / Real.sqrt x ≤ Real.log (10 ^ 7 : ℝ) / Real.sqrt (10 ^ 7 : ℝ) := by
    rcases eq_or_lt_of_le h10 with h1 | h1
    · have hx7 : x = 10 ^ 7 := by rw [hxeq, ← h1]; ring
      rw [hx7]
    · rw [hxeq]
      exact le_of_lt (log_div_sqrt_decay (by norm_num) h1 hla7)
  have hsqrt7 : (3162 : ℝ) < Real.sqrt (10 ^ 7 : ℝ) := by
    have h1 : (3162 : ℝ) ^ 2 < (10 ^ 7 : ℝ) := by norm_num
    have h2 : (Real.sqrt (10 ^ 7 : ℝ)) ^ 2 = (10 ^ 7 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    nlinarith [h1, h2, Real.sqrt_nonneg (10 ^ 7 : ℝ),
      sq_nonneg (Real.sqrt (10 ^ 7 : ℝ) - 3162)]
  have hlog7 : Real.log (10 ^ 7 : ℝ) < 7 * 2.4 := by
    rw [show (10 ^ 7 : ℝ) = (10 : ℝ)^7 by norm_num, Real.log_pow]
    have h7 := mul_lt_mul_of_pos_left log10_lt (show (0 : ℝ) < 7 by norm_num)
    linarith
  have hcomb : Real.log (10 ^ 7 : ℝ) / Real.sqrt (10 ^ 7 : ℝ) < 0.006 := by
    rw [div_lt_iff₀ (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (10 ^ 7 : ℝ)))]
    have hs7 : (0 : ℝ) < Real.sqrt (10 ^ 7 : ℝ) :=
      Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < (10 ^ 7 : ℝ))
    clear hx hlog10 hla7 h10 ht hxeq hM hs7 t
    generalize Real.log (10 ^ 7 : ℝ) = L at hlog7 ⊢
    generalize Real.sqrt (10 ^ 7 : ℝ) = s at hsqrt7 ⊢
    linarith [hlog7, hsqrt7]
  have hsqrtx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  rw [div_le_iff₀ hsqrtx] at hM
  have hle := mul_le_mul_of_nonneg_right (le_of_lt hcomb) (le_of_lt hsqrtx)
  linarith [hM, hle]

-- The gap is positive for n ≥ 4762.
/-- **Positivity of the gap in Breusch's prime interval argument.** For every natural number
$n \ge 4762$, $13n - 16 - 48\log(2100n) - \sqrt{2100n}\,\log(2100n) > 0$, where $\log$ is the
natural logarithm. -/
lemma gap_pos (n : ℕ) (hn : 4762 ≤ n) :
    (13:ℝ)*n - 16 - 48*Real.log ((2100:ℝ)*n)
      - Real.sqrt ((2100:ℝ)*n)*Real.log ((2100:ℝ)*n) > 0 := by
  have hnR : (4762:ℝ) ≤ n := by exact_mod_cast hn
  have hX : (10^7:ℝ) ≤ (2100:ℝ)*n := by
    have hle : (2100:ℝ)*4762 ≤ (2100:ℝ)*n :=
      mul_le_mul_of_nonneg_left hnR (by norm_num)
    norm_num at hle ⊢
    linarith
  have hlog := log_le_sqrt06 ((2100:ℝ)*n) hX
  have hsqrtX : 0 ≤ Real.sqrt ((2100:ℝ)*n) := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((2100:ℝ)*n) * Real.sqrt ((2100:ℝ)*n) = (2100:ℝ)*n :=
    Real.mul_self_sqrt (by positivity)
  have hC : Real.sqrt ((2100:ℝ)*n)*Real.log ((2100:ℝ)*n) ≤ 0.006*((2100:ℝ)*n) := by
    calc Real.sqrt ((2100:ℝ)*n)*Real.log ((2100:ℝ)*n)
        ≤ Real.sqrt ((2100:ℝ)*n)*(0.006*Real.sqrt ((2100:ℝ)*n)) :=
          mul_le_mul_of_nonneg_left hlog hsqrtX
      _ = 0.006*((2100:ℝ)*n) := by linear_combination 0.006 * hsq
  have h48 : 48*Real.log ((2100:ℝ)*n) ≤ 48*(0.006*Real.sqrt ((2100:ℝ)*n)) :=
    mul_le_mul_of_nonneg_left hlog (by norm_num)
  have h2100 : Real.sqrt (2100:ℝ) < 45.83 := by
    have h1 : (2100:ℝ) < (45.83)^2 := by norm_num
    have h2 : (Real.sqrt (2100:ℝ))^2 = (2100:ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [h1, h2, Real.sqrt_nonneg (2100:ℝ),
      sq_nonneg (Real.sqrt (2100:ℝ) - 45.83)]
  have hsqrtmul : Real.sqrt ((2100:ℝ)*(n:ℝ)) = Real.sqrt 2100 * Real.sqrt n :=
    Real.sqrt_mul (by norm_num) _
  have hn_sq : (69:ℝ) ≤ Real.sqrt (n:ℝ) := by
    have h1 : (69:ℝ) = Real.sqrt ((69:ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
    rw [h1]
    apply Real.sqrt_le_sqrt
    have h2 : ((69^2:ℕ):ℝ) ≤ (n:ℝ) := by
      exact_mod_cast (show 69^2 ≤ n from by omega)
    have h3 : (69:ℝ)^2 = ((69^2:ℕ):ℝ) := by norm_num
    linarith [h2, h3]
  have ht0 : (0:ℝ) ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
  have htsq : (Real.sqrt (n:ℝ))^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
  have hnsq : (69:ℝ)*Real.sqrt (n:ℝ) ≤ (Real.sqrt (n:ℝ))^2 := by
    have h := mul_le_mul_of_nonneg_right hn_sq ht0
    nlinarith [h]
  have hXsqrt : Real.sqrt ((2100:ℝ)*(n:ℝ)) ≤ 45.83 * Real.sqrt (n:ℝ) := by
    rw [hsqrtmul]
    have h := mul_le_mul_of_nonneg_right (le_of_lt h2100) ht0
    linarith [h]
  linarith [hC, h48, hXsqrt, htsq, hnsq, hn_sq, hnR]

end MathlibExt.NumberTheory.BreuschWanted.Internal
