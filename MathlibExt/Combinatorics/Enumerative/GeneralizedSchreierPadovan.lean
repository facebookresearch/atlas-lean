/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain

/-!
# Generalized Schreier sets and Padovan-like sequences

This file defines the Schreier counts and Padovan-like sequences of Chu and Vasseur and records
their initial values. It also proves that a sequence satisfying a polynomial recurrence satisfies
the recurrence given by any multiple of that polynomial.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Number of (p, q)-Schreier sets with given maximum.** For natural numbers $p$, $q$ and $n$,
$|S^{p/q}_n|$ is the number of $(p, q)$-Schreier sets with maximum $n$, that is, of subsets
$F \subseteq \{1, \dots, n\}$ with $n \in F$ and $p|F| \le qx$ for every $x \in F$ (equivalently,
$p|F| \le q \min F$).

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def schreierCount (p q n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun F => n ∈ F ∧ ∀ x ∈ F, p * F.card ≤ q * x).card

/-- **Number of maximal $(p, q)$-Schreier sets.** For natural numbers $p$, $q$ and $n$,
$|M^{p/q}_n|$ is the number of maximal $(p, q)$-Schreier sets with maximum $n$, that is, of sets
$F \subseteq \{1, \dots, n\}$ with $n \in F$ and $q \min F = p |F|$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def maximalSchreierCount (p q n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun F =>
    n ∈ F ∧ (∀ x ∈ F, p * F.card ≤ q * x) ∧ ∃ x ∈ F, q * x = p * F.card).card

/-- **Padovan-like sequence for Schreier sets.** For natural numbers $p$ and $q$, the sequence
$a_{p,q,n}$, $n \ge 0$, is defined as follows. If $q \ge 1$ and $n \ge p + q$, then
$a_{p,q,n} = a_{p,q,n-q} + a_{p,q,n-p-q}$. Otherwise, if $p \ge q$, then $a_{p,q,n} = 0$ for
$n < p - q$ and $a_{p,q,n} = 1$ for $n \ge p - q$; and if $p < q$, then $a_{p,q,n} = 1$ for
$n < 2p$ and $a_{p,q,n} = 2$ for $n \ge 2p$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def schreierPadovan (p q : ℕ) : ℕ → ℕ
  | n =>
    if _h : p + q ≤ n ∧ 0 < q then
      schreierPadovan p q (n - q) + schreierPadovan p q (n - p - q)
    else if q ≤ p then (if n + q < p then 0 else 1) else (if n < 2 * p then 1 else 2)
  decreasing_by all_goals omega

/-- **Padovan-like sequence of maximal Schreier sets.** For natural numbers $p$ and $q$, the
sequence $a^{(m)}_{p,q,n}$, $n \ge 0$, is defined as follows. If $q \ge 1$ and $n \ge p + q$, then
$a^{(m)}_{p,q,n} = a^{(m)}_{p,q,n-q} + a^{(m)}_{p,q,n-p-q}$. Otherwise, if $q \le p$, then
$a^{(m)}_{p,q,n}$ is $1$ for $n = p - q$ and $0$ for every other $n$, and if $p < q$, then
$a^{(m)}_{p,q,n}$ is $1$ for $n = 2p$ and $0$ for every other $n$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
def maximalSchreierPadovan (p q : ℕ) : ℕ → ℕ
  | n =>
    if _h : p + q ≤ n ∧ 0 < q then
      maximalSchreierPadovan p q (n - q) + maximalSchreierPadovan p q (n - p - q)
    else if q ≤ p then (if n + q = p then 1 else 0) else (if n = 2 * p then 1 else 0)
  decreasing_by all_goals omega

/-- **Recurrence for the Padovan-like sequence.** For natural numbers $p$, $q$ and $n$ with
$q \ge 1$ and $n \ge p + q$, the Padovan-like sequence satisfies
$a_{p,q,n} = a_{p,q,n-q} + a_{p,q,n-p-q}$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
theorem schreierPadovan_rec {p q n : ℕ} (hq : 0 < q) (hn : p + q ≤ n) :
    schreierPadovan p q n = schreierPadovan p q (n - q) + schreierPadovan p q (n - p - q) := by
  rw [schreierPadovan]
  simp only [hn, hq, and_self, ↓reduceDIte]

/-- **Recurrence for the Padovan-like sequence of maximal Schreier sets.** For natural numbers
$p$, $q$ and $n$ with $q \ge 1$ and $n \ge p + q$, the Padovan-like sequence $a^{(m)}_{p,q,n}$ of
maximal Schreier sets satisfies $a^{(m)}_{p,q,n} = a^{(m)}_{p,q,n-q} + a^{(m)}_{p,q,n-p-q}$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 1. -/
theorem maximalSchreierPadovan_rec {p q n : ℕ} (hq : 0 < q) (hn : p + q ≤ n) :
    maximalSchreierPadovan p q n =
      maximalSchreierPadovan p q (n - q) + maximalSchreierPadovan p q (n - p - q) := by
  rw [maximalSchreierPadovan]
  simp only [hn, hq, and_self, ↓reduceDIte]

/-- **Small values of the Padovan-like sequences.** For $n = 0, 1, \dots, 7$, the Padovan-like
sequence $a_{1,2,n}$ takes the values $1, 1, 2, 2, 3, 4, 5, 7$, and $a_{2,1,n}$ takes the values
$0, 1, 1, 1, 2, 3, 4, 6$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Table 3. -/
theorem schreierPadovan_small :
    (List.range 8).map (schreierPadovan 1 2) = [1, 1, 2, 2, 3, 4, 5, 7] ∧
      (List.range 8).map (schreierPadovan 2 1) = [0, 1, 1, 1, 2, 3, 4, 6] := by
  decide +kernel

/-- **First values of the Padovan-like sequences of maximal Schreier sets.** For
$n = 0, 1, \dots, 7$, the Padovan-like sequence $a^{(m)}_{1,2,n}$ of maximal Schreier sets takes
the values $0, 0, 1, 0, 1, 1, 1, 2$, and $a^{(m)}_{2,1,n}$ takes the values
$0, 1, 0, 0, 1, 1, 1, 2$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Table 4. -/
theorem maximalSchreierPadovan_small :
    (List.range 8).map (maximalSchreierPadovan 1 2) = [0, 0, 1, 0, 1, 1, 1, 2] ∧
      (List.range 8).map (maximalSchreierPadovan 2 1) = [0, 1, 0, 0, 1, 1, 1, 2] := by
  decide +kernel

/-- **Small values of the (1, 2)-Schreier counts.** For $n = 1, 2, 3, 4$, the number $|S^{1/2}_n|$
of $(1, 2)$-Schreier sets with maximum $n$ takes the values $1, 2, 3, 5$, and the number
$|M^{1/2}_n|$ of maximal $(1, 2)$-Schreier sets with maximum $n$ takes the values $0, 1, 1, 1$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Tables 1 and 2. -/
theorem schreierCount_one_two_small :
    (List.range 4).map (fun n => schreierCount 1 2 (n + 1)) = [1, 2, 3, 5] ∧
      (List.range 4).map (fun n => maximalSchreierCount 1 2 (n + 1)) = [0, 1, 1, 1] := by
  decide +kernel

/-- **Sequences satisfying a polynomial.** Let $P = c_0 + c_1 x + \dots + c_r x^r$ be a real
polynomial, where $r$ is the degree of $P$ (and $r = 0$ for $P = 0$). A real sequence
$(a_n)_{n \ge 0}$ satisfies $P$ if $c_0 a_n + c_1 a_{n-1} + \dots + c_r a_{n-r} = 0$ for every
$n \ge r$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 4, Definition 4. -/
def SatisfiesPoly (P : Polynomial ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ n, P.natDegree ≤ n → ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * a (n - i) = 0

/-- **Every sequence satisfies the zero polynomial.** Every real sequence $(a_n)_{n \ge 0}$
satisfies the zero polynomial.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Section 4, Definition 4. -/
theorem satisfiesPoly_zero (a : ℕ → ℝ) : SatisfiesPoly 0 a := by
  intro n _
  simp

/-- **A sequence satisfying a polynomial satisfies its multiples.** Let $P$ and $Q$ be real
polynomials with $P \mid Q$. If a real sequence $(a_n)_{n \ge 0}$ satisfies $P$, then it
satisfies $Q$.

Source: Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier
Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Lemma 5
(`jis-2026-26.2.2-lem-5`). -/
theorem SatisfiesPoly.of_dvd {P Q : Polynomial ℝ} {a : ℕ → ℝ}
    (h : SatisfiesPoly P a) (hPQ : P ∣ Q) : SatisfiesPoly Q a := by
  by_cases hQ : Q = 0
  · subst Q
    exact satisfiesPoly_zero a
  obtain ⟨R, rfl⟩ := hPQ
  obtain ⟨hP, hR⟩ := mul_ne_zero_iff.mp hQ
  intro n hn
  rw [Polynomial.natDegree_mul hP hR] at hn
  -- The recurrence sum at n is linear in the coefficients of the polynomial.
  let L := Polynomial.lsum fun i => LinearMap.mulRight ℝ (a (n - i))
  have eval_eq (S : Polynomial ℝ) :
      L S = ∑ i ∈ Finset.range (S.natDegree + 1), S.coeff i * a (n - i) :=
    S.sum_over_range (f := fun i c => c * a (n - i)) (fun _ => zero_mul _)
  rw [← eval_eq, mul_comm P R, Polynomial.mul_eq_sum_sum, map_sum]
  refine Finset.sum_eq_zero fun j hj => ?_
  have hj' := Polynomial.le_natDegree_of_mem_supp j hj
  have hshift : P.natDegree ≤ n - j := by omega
  rw [Polynomial.sum_over_range P (by simp), map_sum]
  simp only [L, Polynomial.lsum_apply, LinearMap.mulRight_apply, Polynomial.sum_monomial_index,
    zero_mul, mul_assoc, ← Nat.sub_sub, ← Finset.mul_sum, h (n - j) hshift, mul_zero]

end

end MetaMathlibExt
