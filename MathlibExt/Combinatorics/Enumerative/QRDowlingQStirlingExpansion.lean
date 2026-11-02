/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import MathlibExt.Combinatorics.Enumerative.QRWhitneyNumbers
public import MathlibExt.NumberTheory.QRDowlingPolynomial
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

/-- Vanishing above the diagonal from a two-term recurrence. -/
private theorem vanish_of_rec_aux
    (f : ℕ → ℕ → ℂ)
    (h0 : ∀ k : ℕ, f 0 (k + 1) = 0)
    (hs : ∀ a k : ℕ, ∃ A : ℂ, ∃ B : ℂ,
      f (a + 1) (k + 1) = A * f a k + B * f a (k + 1)) :
    ∀ a b : ℕ, a < b → f a b = 0 := by
  intro a
  induction a with
  | zero =>
      intro b hb
      cases b with
      | zero => omega
      | succ c => exact h0 c
  | succ a ih =>
      intro b hb
      cases b with
      | zero => omega
      | succ c =>
          obtain ⟨A, B, hAB⟩ := hs a c
          rw [hAB, ih c (by omega), ih (c + 1) (by omega), mul_zero, mul_zero,
            add_zero]

/-- Factoring one `m` out of a truncated-subtraction power, using vanishing. -/
private theorem mpow_sub_factor_aux
    (m : ℂ) (j k : ℕ) (c : ℂ)
    (hc : j < k + 1 → c = 0) :
    m ^ (j - k) * c = m * (m ^ (j - (k + 1)) * c) := by
  by_cases h : j < k + 1
  · simp [hc h]
  · have he : j - k = (j - (k + 1)) + 1 := by omega
    rw [he, pow_succ]
    ring

/-- Pascal's rule summed over a range. -/
private theorem pascal_sum_aux
    (g : ℕ → ℂ) (a : ℕ) :
    ∑ j ∈ Finset.range (a + 1 + 1), (Nat.choose (a + 1) j : ℂ) * g j =
      ∑ j ∈ Finset.range (a + 1), (Nat.choose a j : ℂ) * g j +
      ∑ j ∈ Finset.range (a + 1), (Nat.choose a j : ℂ) * g (j + 1) := by
  have peel : ∀ (h : ℕ → ℂ) (t : ℕ),
      ∑ i ∈ Finset.range (t + 1), h i =
        h 0 + ∑ c ∈ Finset.range t, h (c + 1) := by
    intro h t
    rw [Finset.sum_range_succ']
    exact add_comm _ _
  have eLHS : ∑ j ∈ Finset.range (a + 1 + 1), (Nat.choose (a + 1) j : ℂ) * g j =
      g 0 + (∑ j ∈ Finset.range (a + 1), (Nat.choose a j : ℂ) * g (j + 1) +
        ∑ j ∈ Finset.range (a + 1), (Nat.choose a (j + 1) : ℂ) * g (j + 1)) := by
    rw [peel _ (a + 1)]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    rw [Nat.choose_succ_succ, Nat.cast_add, add_mul]
  have eR1 : ∑ j ∈ Finset.range (a + 1), (Nat.choose a j : ℂ) * g j =
      g 0 + ∑ c ∈ Finset.range a, (Nat.choose a (c + 1) : ℂ) * g (c + 1) := by
    have h1 := peel (fun i => (Nat.choose a i : ℂ) * g i) a
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul] at h1
    exact h1
  have eSb : ∑ j ∈ Finset.range (a + 1), (Nat.choose a (j + 1) : ℂ) * g (j + 1) =
      ∑ c ∈ Finset.range a, (Nat.choose a (c + 1) : ℂ) * g (c + 1) := by
    rw [Finset.sum_range_succ]
    have hz : (Nat.choose a (a + 1) : ℂ) * g (a + 1) = 0 := by
      rw [Nat.choose_eq_zero_of_lt (by omega : a < a + 1), Nat.cast_zero,
        zero_mul]
    rw [hz, add_zero]
  linear_combination eLHS - eR1 + eSb

/-- **(q, r)-Whitney numbers of the second kind through q-Stirling numbers.** Let
$m, r, q \in \mathbb{C}$ and write $[k + 1]_q = 1 + q + \dots + q^k$. Let $S$ be a complex-valued
function on pairs of natural numbers satisfying the recurrence of the $q$-Stirling numbers of the
second kind: for all $a, k \in \mathbb{N}$, $S(0, 0) = 1$, $S(0, k + 1) = 0$, $S(a + 1, 0) = 0$
and $S(a + 1, k + 1) = q^k S(a, k) + [k + 1]_q \, S(a, k + 1)$. Then for all $a, k \in \mathbb{N}$
the $(q, r)$-Whitney numbers of the second kind satisfy
$$W_{m,r,q}(a, k) = \sum_{j=0}^{a} \binom{a}{j} r^{a-j} m^{j-k} S(j, k),$$
where the exponent $j - k$ is read as $0$ when $j < k$. -/
theorem QRWhitney.whitneySecond_eq_sum_qStirlingSecond
    (m r q : ℂ)
    (qStirlingSecond : ℕ → ℕ → ℂ)
    (hq_zero_zero : qStirlingSecond 0 0 = 1)
    (hq_zero_succ : ∀ k : ℕ, qStirlingSecond 0 (k + 1) = 0)
    (hq_succ_zero : ∀ a : ℕ, qStirlingSecond (a + 1) 0 = 0)
    (hq_succ_succ : ∀ a k : ℕ,
      qStirlingSecond (a + 1) (k + 1) =
        q ^ k * qStirlingSecond a k + QRWhitney.qBrack q (k + 1) * qStirlingSecond a (k + 1)) :
    ∀ a k : ℕ, QRWhitney.whitneySecond m r q a k =
      ∑ j ∈ Finset.range (a + 1),
        (Nat.choose a j : ℂ) * r ^ (a - j) * m ^ (j - k) *
          qStirlingSecond j k := by
  simp only [QRWhitney.qBrack] at hq_succ_succ
  have hW0 : ∀ a : ℕ, QRWhitney.whitneySecond m r q a 0 = r ^ a := by
    intro a
    induction a with
    | zero => rfl
    | succ a ih => rw [QRWhitney.whitneySecond_succ_zero, ih, pow_succ']
  have Svan : ∀ a b : ℕ, a < b → qStirlingSecond a b = 0 :=
    vanish_of_rec_aux qStirlingSecond hq_zero_succ (fun a k =>
      ⟨q ^ k, (∑ i ∈ Finset.range (k + 1), q ^ i), hq_succ_succ a k⟩)
  intro a
  induction a with
  | zero =>
      intro k
      have hsum : (∑ j ∈ Finset.range (0 + 1),
          (Nat.choose 0 j : ℂ) * r ^ (0 - j) * m ^ (j - k) *
            qStirlingSecond j k) = qStirlingSecond 0 k := by
        rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
        simp only [Nat.choose_self, Nat.cast_one, Nat.zero_sub, pow_zero,
          one_mul]
      rw [hsum]
      cases k with
      | zero => rw [QRWhitney.whitneySecond_zero_zero, hq_zero_zero]
      | succ c => rw [QRWhitney.whitneySecond_zero_succ, hq_zero_succ]
  | succ a ih =>
      intro k
      cases k with
      | zero =>
          rw [hW0, Finset.sum_eq_single 0]
          · simp only [hq_zero_zero, Nat.choose_zero_right, Nat.cast_one,
              Nat.sub_zero, pow_zero, one_mul, mul_one]
          · intro j hj hj0
            obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
            simp only [hq_succ_zero c]
            simp
          · intro h
            simp at h
      | succ k =>
          have ihk := ih k
          have ihk1 := ih (k + 1)
          rw [QRWhitney.whitneySecond_succ_succ, QRWhitney.qBrack]
          have pascal : (∑ j ∈ Finset.range (a + 1 + 1),
                (Nat.choose (a + 1) j : ℂ) *
                (r ^ (a + 1 - j) * m ^ (j - (k + 1)) *
                  qStirlingSecond j (k + 1))) =
              (∑ j ∈ Finset.range (a + 1), (Nat.choose a j : ℂ) *
                (r ^ (a + 1 - j) * m ^ (j - (k + 1)) *
                  qStirlingSecond j (k + 1))) +
              (∑ j ∈ Finset.range (a + 1), (Nat.choose a j : ℂ) *
                (r ^ (a + 1 - (j + 1)) * m ^ (j + 1 - (k + 1)) *
                  qStirlingSecond (j + 1) (k + 1))) :=
            pascal_sum_aux _ a
          have e1 : (∑ j ∈ Finset.range (a + 1 + 1),
                (Nat.choose (a + 1) j : ℂ) * r ^ (a + 1 - j) *
                  m ^ (j - (k + 1)) * qStirlingSecond j (k + 1)) =
              (∑ j ∈ Finset.range (a + 1), (Nat.choose a j : ℂ) *
                r ^ (a + 1 - j) * m ^ (j - (k + 1)) *
                qStirlingSecond j (k + 1)) +
              (∑ j ∈ Finset.range (a + 1), (Nat.choose a j : ℂ) *
                r ^ (a - j) * m ^ (j - k) *
                qStirlingSecond (j + 1) (k + 1)) := by
            have f0 : (∑ j ∈ Finset.range (a + 1 + 1),
                  (Nat.choose (a + 1) j : ℂ) * r ^ (a + 1 - j) *
                    m ^ (j - (k + 1)) * qStirlingSecond j (k + 1)) =
                (∑ j ∈ Finset.range (a + 1 + 1),
                  (Nat.choose (a + 1) j : ℂ) *
                  (r ^ (a + 1 - j) * m ^ (j - (k + 1)) *
                    qStirlingSecond j (k + 1))) :=
              Finset.sum_congr rfl (fun j hj => by ring)
            rw [f0, pascal]
            congr 1
            · exact Finset.sum_congr rfl (fun j hj => by ring)
            · apply Finset.sum_congr rfl
              intro j hj
              have h1 : a + 1 - (j + 1) = a - j := by omega
              have h2 : j + 1 - (k + 1) = j - k := by omega
              rw [h1, h2]
              ring
          have e2 : (∑ j ∈ Finset.range (a + 1), (Nat.choose a j : ℂ) *
                r ^ (a + 1 - j) * m ^ (j - (k + 1)) *
                qStirlingSecond j (k + 1)) =
              r * QRWhitney.whitneySecond m r q a (k + 1) := by
            rw [ihk1, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            have haj : j < a + 1 := Finset.mem_range.mp hj
            have hr : r ^ (a + 1 - j) = r * r ^ (a - j) := by
              have h : a + 1 - j = (a - j) + 1 := by omega
              rw [h, pow_succ']
            rw [hr]
            ring
          have e3 : (∑ j ∈ Finset.range (a + 1), (Nat.choose a j : ℂ) *
                r ^ (a - j) * m ^ (j - k) *
                qStirlingSecond (j + 1) (k + 1)) =
              q ^ k * QRWhitney.whitneySecond m r q a k +
                (∑ i ∈ Finset.range (k + 1), q ^ i) *
                  (m * QRWhitney.whitneySecond m r q a (k + 1)) := by
            rw [ihk, ihk1]
            simp only [Finset.mul_sum]
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            have hS := hq_succ_succ j k
            have hA : m ^ (j - k) * qStirlingSecond j (k + 1) =
                m * (m ^ (j - (k + 1)) * qStirlingSecond j (k + 1)) :=
              mpow_sub_factor_aux m j k _ (fun hlt => Svan j (k + 1) hlt)
            calc (Nat.choose a j : ℂ) * r ^ (a - j) * m ^ (j - k) *
                  qStirlingSecond (j + 1) (k + 1)
                = q ^ k * ((Nat.choose a j : ℂ) * r ^ (a - j) * m ^ (j - k) *
                    qStirlingSecond j k) +
                    (∑ i ∈ Finset.range (k + 1), q ^ i) *
                      ((Nat.choose a j : ℂ) * r ^ (a - j) *
                        (m ^ (j - k) * qStirlingSecond j (k + 1))) := by
                    rw [hS]; ring
              _ = q ^ k * ((Nat.choose a j : ℂ) * r ^ (a - j) * m ^ (j - k) *
                    qStirlingSecond j k) +
                    (∑ i ∈ Finset.range (k + 1), q ^ i) *
                      ((Nat.choose a j : ℂ) * r ^ (a - j) *
                        (m * (m ^ (j - (k + 1)) *
                          qStirlingSecond j (k + 1)))) := by
                    rw [hA]
              _ = q ^ k * ((Nat.choose a j : ℂ) * r ^ (a - j) * m ^ (j - k) *
                    qStirlingSecond j k) +
                    (∑ i ∈ Finset.range (k + 1), q ^ i) *
                      (m * ((Nat.choose a j : ℂ) * r ^ (a - j) *
                        m ^ (j - (k + 1)) * qStirlingSecond j (k + 1))) := by
                    ring
          rw [e1, e2, e3]
          ring

/--
**Expansion of the (q, r)-Dowling polynomial in q-Stirling numbers.** Let
$m, r, q, x \in \mathbb{C}$ and $n \in \mathbb{N}$, and write $[k + 1]_q = 1 + q + \dots + q^k$.
Let $S$ be a complex-valued function on pairs of natural numbers satisfying the recurrence of the
$q$-Stirling numbers of the second kind: for all $a, k \in \mathbb{N}$, $S(0, 0) = 1$,
$S(0, k + 1) = 0$, $S(a + 1, 0) = 0$ and $S(a + 1, k + 1) = q^k S(a, k) + [k + 1]_q \, S(a, k + 1)$.
Let $W_{m,r,q}$ be the $(q, r)$-Whitney numbers of the second kind, and let $D_n(x)$ be the
value at $x$ of the $(q, r)$-Dowling polynomial $\sum_{k=0}^{n} W_{m,r,q}(n, k) \, X^k$. Then
$$D_n(x) = \sum_{k=0}^{n} \binom{n}{k} r^{n-k} \sum_{j=0}^{k} m^{k-j} S(k, j) \, x^j.$$

Source: M. M. Mangontarum, *Some Theorems and Applications of the (q,r)-Whitney
Numbers*, Journal of Integer Sequences 20 (2017), Article 17.2.5, theorem equation
`genpriv`, lines 782-789,
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Mangontarum/mango4.tex>.
-/
theorem eval_qrDowlingPolynomial_whitneySecond
    (m r q x : ℂ) (n : ℕ)
    (qStirlingSecond : ℕ → ℕ → ℂ)
    (hq_zero_zero : qStirlingSecond 0 0 = 1)
    (hq_zero_succ : ∀ k : ℕ, qStirlingSecond 0 (k + 1) = 0)
    (hq_succ_zero : ∀ a : ℕ, qStirlingSecond (a + 1) 0 = 0)
    (hq_succ_succ : ∀ a k : ℕ,
      qStirlingSecond (a + 1) (k + 1) =
        q ^ k * qStirlingSecond a k + QRWhitney.qBrack q (k + 1) * qStirlingSecond a (k + 1)) :
    Polynomial.eval x (qrDowlingPolynomial (QRWhitney.whitneySecond m r q) n) =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * r ^ (n - k) *
          ∑ j ∈ Finset.range (k + 1),
            m ^ (k - j) * qStirlingSecond k j * x ^ j := by
  have Svan : ∀ a b : ℕ, a < b → qStirlingSecond a b = 0 :=
    vanish_of_rec_aux qStirlingSecond hq_zero_succ (fun a k =>
      ⟨q ^ k, QRWhitney.qBrack q (k + 1), hq_succ_succ a k⟩)
  have Wkey := QRWhitney.whitneySecond_eq_sum_qStirlingSecond m r q qStirlingSecond
    hq_zero_zero hq_zero_succ hq_succ_zero hq_succ_succ
  rw [qrDowlingPolynomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have expand : ∀ k ∈ Finset.range (n + 1),
      (Nat.choose n k : ℂ) * r ^ (n - k) *
        (∑ j ∈ Finset.range (k + 1),
          m ^ (k - j) * qStirlingSecond k j * x ^ j) =
      ∑ t ∈ Finset.range (n + 1),
        (((Nat.choose n k : ℂ) * r ^ (n - k) * m ^ (k - t) *
          qStirlingSecond k t) * x ^ t) := by
    intro k hk
    have hkn : k < n + 1 := Finset.mem_range.mp hk
    have hsub : (∑ j ∈ Finset.range (k + 1),
          m ^ (k - j) * qStirlingSecond k j * x ^ j) =
        ∑ t ∈ Finset.range (n + 1),
          m ^ (k - t) * qStirlingSecond k t * x ^ t := by
      have hsub12 : Finset.range (k + 1) ⊆ Finset.range (n + 1) := by
        intro t ht
        simp only [Finset.mem_range] at ht ⊢
        omega
      apply Finset.sum_subset hsub12
      intro t ht1 ht2
      have hkt : k < t := by
        simp only [Finset.mem_range, not_lt] at ht2
        omega
      rw [Svan k t hkt]
      simp
    rw [hsub, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  calc ∑ k ∈ Finset.range (n + 1), QRWhitney.whitneySecond m r q n k * x ^ k
      = ∑ t ∈ Finset.range (n + 1),
          (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℂ) * r ^ (n - k) *
            m ^ (k - t) * qStirlingSecond k t) * x ^ t := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [Wkey n t, Finset.sum_mul]
    _ = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℂ) * r ^ (n - k) *
          ∑ j ∈ Finset.range (k + 1),
            m ^ (k - j) * qStirlingSecond k j * x ^ j := by
        have e1 : (∑ t ∈ Finset.range (n + 1),
              (∑ k ∈ Finset.range (n + 1), (Nat.choose n k : ℂ) * r ^ (n - k) *
                m ^ (k - t) * qStirlingSecond k t) * x ^ t) =
            ∑ t ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              (((Nat.choose n k : ℂ) * r ^ (n - k) * m ^ (k - t) *
                qStirlingSecond k t) * x ^ t) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.sum_mul]
        have e2 : (∑ t ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              (((Nat.choose n k : ℂ) * r ^ (n - k) * m ^ (k - t) *
                qStirlingSecond k t) * x ^ t)) =
            ∑ k ∈ Finset.range (n + 1), ∑ t ∈ Finset.range (n + 1),
              (((Nat.choose n k : ℂ) * r ^ (n - k) * m ^ (k - t) *
                qStirlingSecond k t) * x ^ t) :=
          Finset.sum_comm
        rw [e1, e2]
        apply Finset.sum_congr rfl
        intro k hk
        exact (expand k hk).symm

/-- A family with the `(q, r)`-Whitney recurrence of the second kind is
`QRWhitney.whitneySecond`. -/
private theorem whitneySecond_eq_of_rec
    (q m r : ℂ)
    (W : ℕ → ℕ → ℂ)
    (hW_zero_zero : W 0 0 = 1)
    (hW_zero_succ : ∀ k : ℕ, W 0 (k + 1) = 0)
    (hW_succ_zero : ∀ a : ℕ, W (a + 1) 0 = r ^ (a + 1))
    (hW_succ_succ : ∀ a k : ℕ,
      W (a + 1) (k + 1) =
        q ^ k * W a k + (m * (∑ i ∈ Finset.range (k + 1), q ^ i) + r) * W a (k + 1)) :
    ∀ a k : ℕ, W a k = QRWhitney.whitneySecond m r q a k := by
  intro a
  induction a with
  | zero =>
      intro k
      cases k with
      | zero => rw [hW_zero_zero, QRWhitney.whitneySecond_zero_zero]
      | succ k => rw [hW_zero_succ, QRWhitney.whitneySecond_zero_succ]
  | succ a ih =>
      intro k
      cases k with
      | zero =>
          have h0 : W a 0 = r ^ a := by
            cases a with
            | zero => rw [hW_zero_zero, pow_zero]
            | succ a => exact hW_succ_zero a
          rw [hW_succ_zero, QRWhitney.whitneySecond_succ_zero, ← ih 0, h0, pow_succ']
      | succ k =>
          rw [hW_succ_succ, QRWhitney.whitneySecond_succ_succ, ih k, ih (k + 1)]
          rfl

/--
**(q, r)-Dowling polynomial expansion from the defining recurrences.** Let
$q, m, r, x \in \mathbb{C}$ and $n \in \mathbb{N}$, and write $[k + 1]_q = \sum_{i=0}^{k} q^i$.
Let $S$ and $W$ be complex-valued functions on pairs of natural numbers, and let $D(a, y)$ be a
complex-valued function of $a \in \mathbb{N}$ and $y \in \mathbb{C}$, such that for all
$a, k \in \mathbb{N}$ and $y \in \mathbb{C}$: $S(0, 0) = 1$, $S(0, k + 1) = 0$, $S(a + 1, 0) = 0$
and $S(a + 1, k + 1) = q^k S(a, k) + [k + 1]_q \, S(a, k + 1)$ (the recurrence of the
$q$-Stirling numbers of the second kind); $W(0, 0) = 1$, $W(0, k + 1) = 0$,
$W(a + 1, 0) = r^{a + 1}$ and $W(a + 1, k + 1) = q^k W(a, k) + (m [k + 1]_q + r) \, W(a, k + 1)$
(the recurrence of the $(q, r)$-Whitney numbers of the second kind); and
$D(a, y) = \sum_{k=0}^{a} W(a, k) \, y^k$ (the $(q, r)$-Dowling polynomial). Then
$$D(n, x) = \sum_{k=0}^{n} \binom{n}{k} r^{n-k} \sum_{j=0}^{k} m^{k-j} S(k, j) \, x^j.$$

Proves `Wanted` entry `q_r_dowling_polynomial_q_stirling_expansion`.

Source: M. M. Mangontarum, *Some Theorems and Applications of the (q,r)-Whitney
Numbers*, Journal of Integer Sequences 20 (2017), Article 17.2.5, theorem equation
`genpriv`, lines 782-789,
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Mangontarum/mango4.tex>.
-/
theorem q_r_dowling_polynomial_q_stirling_expansion
    (q m r x : ℂ) (n : ℕ)
    (qStirlingSecond whitneySecond : ℕ → ℕ → ℂ)
    (dowlingPolynomial : ℕ → ℂ → ℂ)
    (hq_zero_zero : qStirlingSecond 0 0 = 1)
    (hq_zero_succ : ∀ k : ℕ, qStirlingSecond 0 (k + 1) = 0)
    (hq_succ_zero : ∀ a : ℕ, qStirlingSecond (a + 1) 0 = 0)
    (hq_succ_succ : ∀ a k : ℕ,
      qStirlingSecond (a + 1) (k + 1) =
        q ^ k * qStirlingSecond a k +
          (∑ i ∈ Finset.range (k + 1), q ^ i) * qStirlingSecond a (k + 1))
    (hW_zero_zero : whitneySecond 0 0 = 1)
    (hW_zero_succ : ∀ k : ℕ, whitneySecond 0 (k + 1) = 0)
    (hW_succ_zero : ∀ a : ℕ, whitneySecond (a + 1) 0 = r ^ (a + 1))
    (hW_succ_succ : ∀ a k : ℕ,
      whitneySecond (a + 1) (k + 1) =
        q ^ k * whitneySecond a k +
          (m * (∑ i ∈ Finset.range (k + 1), q ^ i) + r) *
            whitneySecond a (k + 1))
    (hD : ∀ a : ℕ, ∀ y : ℂ,
      dowlingPolynomial a y =
        ∑ k ∈ Finset.range (a + 1), whitneySecond a k * y ^ k) :
    dowlingPolynomial n x =
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℂ) * r ^ (n - k) *
          ∑ j ∈ Finset.range (k + 1),
            m ^ (k - j) * qStirlingSecond k j * x ^ j := by
  have hW := whitneySecond_eq_of_rec q m r whitneySecond hW_zero_zero hW_zero_succ
    hW_succ_zero hW_succ_succ
  have hDx : dowlingPolynomial n x =
      Polynomial.eval x (qrDowlingPolynomial (QRWhitney.whitneySecond m r q) n) := by
    rw [hD n x, qrDowlingPolynomial, Polynomial.eval_finsetSum]
    simp only [hW, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
  rw [hDx]
  exact eval_qrDowlingPolynomial_whitneySecond m r q x n qStirlingSecond
    hq_zero_zero hq_zero_succ hq_succ_zero hq_succ_succ

end MetaMathlibExt
