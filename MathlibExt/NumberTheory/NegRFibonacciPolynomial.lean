/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic.Ring

/-! # An explicit sum for the negative-order Fibonacci polynomials -/

namespace MetaMathlibExt

@[expose] public section

/-- **The (-r)-Fibonacci polynomials.** Let $A$ be a commutative ring, $r$ a natural number,
$x \in A$ and $y$ a unit of $A$. The values $U_n = U^{(-r)}_n(x, y) \in A$ of the
$(-r)$-Fibonacci polynomials are defined for $n \ge 0$ by $U_0 = 0$, $U_1 = 1$, $U_n = 0$ for
$2 \le n \le r$, and, when $r \ge 1$, $U_{n+1} = y^{-1} U_{n-r+1} - y^{-1} x U_{n-r}$ for
$n \ge r$. When $r = 0$, $U_n = 0$ for every $n \ge 2$.

The paper takes $r \ge 2$; the case $r = 0$ only makes the definition total.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public def negRFibonacci {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) : ℕ → A
  | 0 => 0
  | n + 1 =>
    if n = 0 then 1
    else if n < r ∨ r = 0 then 0
    else (↑y⁻¹ : A) * negRFibonacci r x y (n - r + 1) - ↑y⁻¹ * x * negRFibonacci r x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- **The zeroth (-r)-Fibonacci polynomial.** For every commutative ring $A$, natural number
$r$, $x \in A$ and unit $y$ of $A$, the $(-r)$-Fibonacci polynomial satisfies
$U^{(-r)}_0(x, y) = 0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public theorem negRFibonacci_zero {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) :
    negRFibonacci r x y 0 = 0 := by
  rw [negRFibonacci]

/-- **The first (-r)-Fibonacci polynomial.** For every commutative ring $A$, natural number
$r$, $x \in A$ and unit $y$ of $A$, the $(-r)$-Fibonacci polynomial satisfies
$U^{(-r)}_1(x, y) = 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public theorem negRFibonacci_one {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) :
    negRFibonacci r x y 1 = 1 := by
  rw [negRFibonacci]
  simp

/-- **The (-r)-Fibonacci polynomials vanish at indices 2 to r.** Let $A$ be a commutative ring,
$x \in A$ and $y$ a unit of $A$. For natural numbers $r$ and $n$ with $1 \le n < r$, the
$(-r)$-Fibonacci polynomial satisfies $U^{(-r)}_{n+1}(x, y) = 0$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3. -/
public theorem negRFibonacci_succ_of_lt {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (h1 : 1 ≤ n) (h : n < r) : negRFibonacci r x y (n + 1) = 0 := by
  rw [negRFibonacci]
  simp [show n ≠ 0 by omega, h]

/-- **Recurrence for the (-r)-Fibonacci polynomials.** Let $A$ be a commutative ring, $x \in A$
and $y$ a unit of $A$, let $r$ and $n$ be natural numbers with $1 \le r \le n$, and write
$U_m = U^{(-r)}_m(x, y)$. Then $U_{n+1} = y^{-1} U_{n-r+1} - y^{-1} x U_{n-r}$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 3, Equation (7). -/
public theorem negRFibonacci_succ_of_le {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (hr : 1 ≤ r) (h : r ≤ n) :
    negRFibonacci r x y (n + 1)
      = ↑y⁻¹ * negRFibonacci r x y (n - r + 1) - ↑y⁻¹ * x * negRFibonacci r x y (n - r) := by
  rw [negRFibonacci]
  simp [show n ≠ 0 by omega, show ¬n < r by omega, show r ≠ 0 by omega]

end

namespace negRFibonacci_succ_eq_sum'

variable {A : Type*} [CommRing A]

-- The term indexed by the number of steps of length r + 1.
private def weight (r : ℕ) (u v : A) (n k : ℕ) : A :=
  if r ∣ n - k then (((n - k) / r).choose k : A) * u ^ ((n - k) / r) * v ^ k else 0

private lemma weight_eq_zero {r n k : ℕ} (u v : A) (h : (n - k) / r < k) :
    weight r u v n k = 0 := by
  simp [weight, Nat.choose_eq_zero_of_lt h]

private lemma weight_add_zero {r : ℕ} (hr : 0 < r) (u v : A) (n : ℕ) :
    weight r u v (n + r) 0 = u * weight r u v n 0 := by
  by_cases h : r ∣ n <;> simp [weight, h, Nat.add_div_right _ hr, pow_succ']

-- Pascal's rule sorts the paths according to the length of their last step.
private lemma weight_add_succ {r : ℕ} (hr : 0 < r) (u v : A) (n k : ℕ) :
    weight r u v (n + 1 + r) (k + 1) =
      u * weight r u v (n + 1) (k + 1) + u * v * weight r u v n k := by
  by_cases hk : k ≤ n
  · have hsub : n + 1 + r - (k + 1) = n - k + r := by omega
    by_cases hd : r ∣ n - k
    · simp [weight, hsub, hd, Nat.add_div_right _ hr, Nat.choose_succ_succ, pow_succ]
      ring
    · simp [weight, hsub, hd]
  · have hdiv : (n + 1 + r - (k + 1)) / r = 0 := Nat.div_eq_of_lt (by omega)
    have hnk : n - k = 0 := by omega
    have hk₀ : 0 < k := by omega
    simp [weight, hdiv, hnk, Nat.choose_eq_zero_of_lt hk₀]

-- Allow a larger cutoff so that the two sums in the recurrence can be aligned.
private lemma eq_sum_weight {r : ℕ} (hr : 2 ≤ r) (x : A) (y : Aˣ) (n m : ℕ)
    (hm : n / r < m) :
    negRFibonacci r x y (n + 1) = ∑ k ∈ Finset.range m, weight r (↑y⁻¹ : A) (-x) n k := by
  have hr' : 0 < r := by omega
  induction n using Nat.strong_induction_on generalizing m with
  | ind n ih =>
    by_cases hn : n ≤ r
    · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.zero_lt_of_lt hm))]
      · by_cases hn₀ : n = 0
        · subst n
          simp [negRFibonacci_one, weight]
        · by_cases hnr : n = r
          · subst n
            simp [negRFibonacci_succ_of_le x y (by omega : 1 ≤ r) (le_refl r),
              negRFibonacci_zero, negRFibonacci_one, weight, Nat.div_self hr']
          · have hlt : n < r := by omega
            have hnd : ¬r ∣ n := fun hd => (Nat.le_of_dvd (by omega) hd).not_gt hlt
            simp [negRFibonacci_succ_of_lt x y (by omega : 1 ≤ n) hlt, weight, hnd]
      · intro k _ hk
        apply weight_eq_zero
        rw [Nat.div_eq_of_lt (by omega : n - k < r)]
        omega
    · obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 + r := ⟨n - (r + 1), by omega⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hm)
      rw [Nat.add_div_right _ hr'] at hm
      have ht : t / r ≤ (t + 1) / r := Nat.div_le_div_right (by omega)
      rw [negRFibonacci_succ_of_le x y (by omega) (by omega), Nat.add_sub_cancel,
        ih (t + 1) (by omega) (m + 1) (by omega), ih t (by omega) m (by omega)]
      rw [Finset.sum_range_succ' (weight r (↑y⁻¹ : A) (-x) (t + 1 + r)),
        Finset.sum_range_succ' (weight r (↑y⁻¹ : A) (-x) (t + 1))]
      simp_rw [weight_add_succ hr', weight_add_zero hr', Finset.sum_add_distrib,
        ← Finset.mul_sum]
      ring

end negRFibonacci_succ_eq_sum'

/-- **Explicit sum for the (-r)-Fibonacci polynomials, second form.** Let $A$ be a commutative
ring, $r \ge 2$, $x \in A$ and $y$ a unit of $A$, and write $U_n = U^{(-r)}_n(x, y)$. For every
$n \ge 0$, $U_{n+1}$ is the sum of $\binom{(n-k)/r}{k} y^{-(n-k)/r} (-x)^k$ over the integers
$k$ with $0 \le k \le \lfloor n/r \rfloor$ and $r \mid n - k$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Theorem 6 (`integers-2025-A38-thm-6`). -/
public theorem negRFibonacci_succ_eq_sum' {A : Type*} [CommRing A] {r : ℕ}
    (hr : 2 ≤ r) (x : A) (y : Aˣ) (n : ℕ) :
    negRFibonacci r x y (n + 1)
      = ∑ k ∈ (Finset.range (n / r + 1)).filter (fun k => r ∣ n - k),
          ((((n - k) / r).choose k : ℕ) : A) * (↑y⁻¹ : A) ^ ((n - k) / r) * (-x) ^ k := by
  rw [Finset.sum_filter]
  exact negRFibonacci_succ_eq_sum'.eq_sum_weight hr x y n _ (Nat.lt_succ_self _)

end MetaMathlibExt
