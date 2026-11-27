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

/-!
# Negative-order Fibonacci polynomials and their companion sequence

Over a commutative ring, for a natural number `r ≥ 2`, an element `x` and a unit `y`,
`negRFibonacci_succ_eq_sum'` gives a binomial sum for the term at `n + 1` for every natural
number `n`. For `n ≥ r`, `negRLucas_eq` expresses the companion term at `n` in terms of the
Fibonacci terms at `n + 1` and `n - r`. Unlike the paper, the identity does not require `x`
to be invertible.

## References

* Sadjia Abbad and Hacène Belbachir, *The r-Fibonacci Polynomial and Its Companion Sequences
  Linked with Some Classical Sequences*, INTEGERS 25 (2025), Article A38, pp. 1–20,
  Definitions 3 and 4, Theorem 6, and Proposition 1, Equation (8).
* Hacène Belbachir and Farid Bencherif, *Linear recurrent sequences and powers of a square
  matrix*, INTEGERS 6 (2006), Article A12, pp. 1–17, Theorem 3. Abbad and Belbachir use this
  theorem in their proof of Proposition 1; the proof here uses the recurrence directly.
-/

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

/-- **Companion sequence of the $(-r)$-Fibonacci polynomials.** Let $A$ be a commutative ring,
$r$ a natural number, $x \in A$ and $y$ a unit of $A$. The companion sequence
$V^{(-r)}_n(x, y) \in A$, $n \ge 0$, is defined by $V^{(-r)}_0 = r + 1$ and, if $r \ge 1$, by
$V^{(-r)}_n = 0$ for $1 \le n < r$, $V^{(-r)}_r = r y^{-1}$ and
$V^{(-r)}_{n+1} = y^{-1} V^{(-r)}_{n-r+1} - y^{-1} x V^{(-r)}_{n-r}$ for $n \ge r$. If $r = 0$,
then $V^{(-r)}_n = 0$ for all $n \ge 1$.

The paper takes $r \ge 2$; the case $r = 0$ only makes the definition total.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public def negRLucas {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) : ℕ → A
  | 0 => (r : A) + 1
  | n + 1 =>
    if r = 0 ∨ n + 1 < r then 0
    else if n + 1 = r then (r : A) * ↑y⁻¹
    else (↑y⁻¹ : A) * negRLucas r x y (n - r + 1) - ↑y⁻¹ * x * negRLucas r x y (n - r)
termination_by n => n
decreasing_by all_goals omega

/-- **Zeroth term of the companion sequence $V^{(-r)}$.** Let $A$ be a commutative ring, $r$ a
natural number, $x \in A$ and $y$ a unit of $A$. The companion sequence of the
$(-r)$-Fibonacci polynomials satisfies $V^{(-r)}_0(x, y) = r + 1$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_zero {A : Type*} [CommRing A] (r : ℕ) (x : A) (y : Aˣ) :
    negRLucas r x y 0 = (r : A) + 1 := by
  rw [negRLucas]

/-- **Vanishing initial terms of the companion sequence $V^{(-r)}$.** Let $A$ be a commutative
ring, $x \in A$ and $y$ a unit of $A$. For natural numbers $r$ and $n$ with $n + 1 < r$, the
companion sequence of the $(-r)$-Fibonacci polynomials satisfies $V^{(-r)}_{n+1}(x, y) = 0$;
that is, $V^{(-r)}_m(x, y) = 0$ for $1 \le m < r$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_succ_of_lt {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (h : n + 1 < r) : negRLucas r x y (n + 1) = 0 := by
  rw [negRLucas]
  simp [h]

/-- **The $r$-th term of the companion sequence $V^{(-r)}$.** Let $A$ be a commutative ring,
$r \ge 1$ a natural number, $x \in A$ and $y$ a unit of $A$. The companion sequence of the
$(-r)$-Fibonacci polynomials satisfies $V^{(-r)}_r(x, y) = r y^{-1}$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_self {A : Type*} [CommRing A] {r : ℕ} (x : A) (y : Aˣ)
    (hr : 1 ≤ r) : negRLucas r x y r = (r : A) * ↑y⁻¹ := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  rw [negRLucas]
  simp

/-- **Recurrence for the companion sequence $V^{(-r)}$.** Let $A$ be a commutative ring, $x \in A$
and $y$ a unit of $A$. For natural numbers $r$ and $n$ with $1 \le r \le n$, the companion
sequence of the $(-r)$-Fibonacci polynomials satisfies
$V^{(-r)}_{n+1}(x, y) = y^{-1} V^{(-r)}_{n-r+1}(x, y) - y^{-1} x V^{(-r)}_{n-r}(x, y)$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Definition 4. -/
public theorem negRLucas_succ_of_le {A : Type*} [CommRing A] {r n : ℕ} (x : A) (y : Aˣ)
    (hr : 1 ≤ r) (h : r ≤ n) :
    negRLucas r x y (n + 1)
      = ↑y⁻¹ * negRLucas r x y (n - r + 1) - ↑y⁻¹ * x * negRLucas r x y (n - r) := by
  rw [negRLucas]
  simp [show r ≠ 0 by omega, show ¬n + 1 < r by omega, show n + 1 ≠ r by omega]

/-- **The companion sequence in terms of the $(-r)$-Fibonacci polynomials.** Let $A$ be a
commutative ring, $r \ge 2$ a natural number, $x \in A$ and $y$ a unit of $A$, and let
$U^{(-r)}_n(x, y)$ be the $(-r)$-Fibonacci polynomials and $V^{(-r)}_n(x, y)$ their companion
sequence. For every natural number $n \ge r$,
$V^{(-r)}_n(x, y) = r \, U^{(-r)}_{n+1}(x, y) - x y^{-1} U^{(-r)}_{n-r}(x, y)$.

The paper takes $x$ a unit; the identity holds for every $x$.

Source: Abbad and Belbachir, *The r-Fibonacci Polynomial and Its Companion
Sequences Linked with Some Classical Sequences*, INTEGERS 25 (2025),
Article A38, Proposition 1, Equation (8) (`integers-2025-A38-prop-1`). -/
public theorem negRLucas_eq {A : Type*} [CommRing A] {r n : ℕ} (hr : 2 ≤ r)
    (hn : r ≤ n) (x : A) (y : Aˣ) :
    negRLucas r x y n =
      r * negRFibonacci r x y (n + 1) - x * ↑y⁻¹ * negRFibonacci r x y (n - r) := by
  let U := negRFibonacci r x y
  let V := negRLucas r x y
  let a : A := ↑y⁻¹
  let b := a * x
  let D (k : ℕ) := V k - (r : A) * U (k + 1)
  have hr' : 1 ≤ r := by omega
  -- With truncated subtraction, both recurrence terms vanish below the first step.
  have hU (k : ℕ) : U (k + 1) = (if k = 0 then 1 else 0) +
      a * U (k + 1 - r) - b * U (k - r) := by
    by_cases hk : r ≤ k
    · simpa only [U, a, b, ite_eq_right (by omega : k ≠ 0), zero_add,
        show k + 1 - r = k - r + 1 by omega] using negRFibonacci_succ_of_le x y hr' hk
    · simp only [show k + 1 - r = 0 by omega, show k - r = 0 by omega, U,
        negRFibonacci_zero, mul_zero, add_zero, sub_zero]
      by_cases h : k = 0
      · simp [h, negRFibonacci_one]
      · simp [h, negRFibonacci_succ_of_lt x y (by omega : 1 ≤ k) (by omega : k < r)]
  have hD (k : ℕ) : D k = (if k = 0 then 1 else 0) - b * U (k - r) := by
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      cases k with
      | zero => simp [D, V, U, negRLucas_zero, negRFibonacci_one, negRFibonacci_zero]
      | succ k =>
        by_cases hk : r ≤ k
        · have hs : k + 1 - r = k - r + 1 := by omega
          calc
            D (k + 1) = a * D (k - r + 1) - b * D (k - r) := by
              simp only [D, V, U, a, b, negRLucas_succ_of_le x y hr' hk,
                negRFibonacci_succ_of_le x y hr' (by omega : r ≤ k + 1), hs]
              ring
            _ = _ := by
              rw [ih (k - r + 1) (by omega), ih (k - r) (by omega), hs, hU (k - r)]
              simp only [Nat.succ_ne_zero, ite_false]
              ring
        · by_cases he : k + 1 = r
          · subst r
            simp [D, V, U, negRLucas_self x y hr', negRFibonacci_succ_of_le x y hr' le_rfl,
              negRFibonacci_one, negRFibonacci_zero]
          · have hlt : k + 1 < r := by omega
            simp [D, V, U, negRLucas_succ_of_lt x y hlt,
              negRFibonacci_succ_of_lt x y (Nat.succ_pos k) hlt,
              show k + 1 - r = 0 by omega, negRFibonacci_zero]
  have heq := hD n
  simp only [D, U, V, b, a, ite_eq_right (by omega : n ≠ 0)] at heq
  rw [sub_eq_iff_eq_add] at heq
  rw [heq]
  ring

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
