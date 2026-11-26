/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Data.Int.Basic
import Mathlib.Order.Int.LeastGreatest
import Mathlib.Tactic.Linarith

/-!
# Signs and difference-inverses of extraTribs

An extraTrib obeys the Tribonacci recurrence on all integer indices and is eventually positive.
Three consecutive terms with the same strict sign force that sign at all later indices. An
extraTrib has a unique rational difference-inverse, with integrality determined by its parities.
-/

namespace MetaMathlibExt

/-- **ExtraTribs.** An extraTrib is a two-sided integer sequence
$S \colon \mathbb{Z} \to \mathbb{Z}$ that follows the Tribonacci rule
$S(n+3) = S(n+2) + S(n+1) + S(n)$ for every $n \in \mathbb{Z}$ and whose terms are eventually
positive: there is an integer $N$ with $S(n) > 0$ for all $n \ge N$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Section 4. -/
@[expose] public def IsExtraTrib (S : ℤ → ℤ) : Prop :=
  (∀ n, S (n + 3) = S (n + 2) + S (n + 1) + S n) ∧ ∃ N, ∀ n ≥ N, 0 < S n

namespace extraTrib_left_extension

/-- A property closed under addition propagates forward from three consecutive terms. -/
private theorem propagate {S : ℤ → ℤ}
    (rec : ∀ i, S (i + 3) = S (i + 2) + S (i + 1) + S i)
    (P : ℤ → Prop) (hadd : ∀ {a b}, P a → P b → P (a + b)) {n : ℤ}
    (h : P (S n) ∧ P (S (n + 1)) ∧ P (S (n + 2))) (m : ℤ) (hm : n ≤ m) : P (S m) := by
  suffices P (S m) ∧ P (S (m + 1)) ∧ P (S (m + 2)) from this.1
  induction m, hm using Int.leInduction with
  | base => exact h
  | succ m _ ih =>
    rw [show m + 1 + 1 = m + 2 by omega, show m + 1 + 2 = m + 3 by omega, rec]
    exact ⟨ih.2.1, ih.2.2, hadd (hadd ih.2.2 ih.2.1) ih.1⟩

end extraTrib_left_extension

/-- **Signs of an extraTrib to the left.** Let $S$ be an extraTrib. Then $S(k) < 0$ for some
integer $k$, and whenever $S(k) < 0$, for every integer $n$ with $n + 2 < k$ the three terms
$S(n)$, $S(n+1)$, $S(n+2)$ are neither all positive nor all negative.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Lemma 19 (`jis-2025-25.5.4-lem-19`). -/
public theorem extraTrib_left_extension (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    (∃ k, S k < 0) ∧ ∀ k, S k < 0 → ∀ n, n + 2 < k →
      ¬ (0 < S n ∧ 0 < S (n + 1) ∧ 0 < S (n + 2)) ∧
        ¬ (S n < 0 ∧ S (n + 1) < 0 ∧ S (n + 2) < 0) := by
  obtain ⟨rec, N, hN⟩ := hS
  have noNonpos (n : ℤ) : ¬ (S n ≤ 0 ∧ S (n + 1) ≤ 0 ∧ S (n + 2) ≤ 0) := by
    intro h
    exact (hN (max n N) (le_max_right ..)).not_ge
      (extraTrib_left_extension.propagate rec (· ≤ 0) add_nonpos h (max n N) (le_max_left ..))
  constructor
  · by_contra h
    have hnonneg (i : ℤ) : 0 ≤ S i := le_of_not_gt (fun hi => h ⟨i, hi⟩)
    -- At an attained minimum the three predecessors must all be zero.
    obtain ⟨_, ⟨j, rfl⟩, hmin⟩ := Int.exists_least_of_bdd (P := fun v => ∃ i, S i = v)
      ⟨0, fun _ ⟨i, hi⟩ => hi ▸ hnonneg i⟩ ⟨S 0, 0, rfl⟩
    let n := j - 3
    have hsum := rec n
    rw [show n + 3 = j by dsimp [n]; omega] at hsum
    have h₀ := hmin _ ⟨n, rfl⟩
    have h₁ := hmin _ ⟨n + 1, rfl⟩
    have h₂ := hmin _ ⟨n + 2, rfl⟩
    have hj := hnonneg j
    exact noNonpos n ⟨by omega, by omega, by omega⟩
  · intro k hk n hn
    constructor
    · intro h
      exact hk.asymm (extraTrib_left_extension.propagate rec (0 < ·) add_pos h k (by omega))
    · rintro ⟨h₀, h₁, h₂⟩
      exact noNonpos n ⟨h₀.le, h₁.le, h₂.le⟩


/-- Tribonacci parities have period four; a mismatch two apart forces a rotation of EEOO. -/
private theorem extraTrib_parity_two_apart_iff {S : ℤ → ℤ}
    (rec : ∀ n, S (n + 3) = S (n + 2) + S (n + 1) + S n) :
    (∀ n, S (n + 2) % 2 = S n % 2) ↔
      ¬ ∃ k : ℤ, ∀ n, (Even (S n) ↔ (n - k) % 4 < 2) := by
  let p (n : ℤ) := S n % 2
  have period (n : ℤ) : p (n + 4) = p n := by
    have h₀ := rec n
    have h₁ := rec (n + 1)
    simp only [add_assoc, Int.reduceAdd] at h₁
    dsimp [p]
    omega
  -- Reduce modulo four in either direction, including for negative indices.
  have shift (k q : ℤ) : p (k + 4 * q) = p k := by
    induction q using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [show k + 4 * ((i : ℤ) + 1) = (k + 4 * i) + 4 by omega, period, ih]
    | pred i ih =>
      rw [← period (k + 4 * (-(i : ℤ) - 1))]
      simpa only [show k + 4 * (-(i : ℤ) - 1) + 4 = k + 4 * (-(i : ℤ)) by omega] using ih
  have rotated (k : ℤ) (h₀ : p k = 0) (h₁ : p (k + 1) = 0) (h₂ : p (k + 2) = 1)
      (h₃ : p (k + 3) = 1) : ∀ n, (Even (S n) ↔ (n - k) % 4 < 2) := by
    intro n
    let r := (n - k) % 4
    have hr : n = (k + r) + 4 * ((n - k) / 4) := by dsimp [r]; omega
    have hp : p n = p (k + r) := by rw [hr, shift]
    rw [Int.even_iff]
    change p n = 0 ↔ r < 2
    rw [hp]
    have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by dsimp [r]; omega
    rcases hr' with h | h | h | h <;> rw [h] <;> simp [h₀, h₁, h₂, h₃]
  constructor
  · intro h ⟨k, hk⟩
    have h₀ : Even (S k) := (hk k).2 (by omega)
    have h₂ : ¬ Even (S (k + 2)) := by
      intro he
      have := (hk (k + 2)).1 he
      omega
    exact h₂ (Int.even_iff.mpr ((h k).trans (Int.even_iff.mp h₀)))
  · intro h n
    change p (n + 2) = p n
    by_contra hne
    have weight : (p n + p (n + 1) + p (n + 2) + p (n + 3)) % 2 = 0 := by
      have := rec n
      dsimp [p]
      omega
    have bounds (i : ℤ) : 0 ≤ p i ∧ p i < 2 := by dsimp [p]; omega
    have h₀ := bounds n
    have h₁ := bounds (n + 1)
    have h₂ := bounds (n + 2)
    have h₃ := bounds (n + 3)
    have h₄ := period n
    have h₅ : p (n + 5) = p (n + 1) := by
      simpa only [add_assoc, Int.reduceAdd] using period (n + 1)
    have h₆ : p (n + 6) = p (n + 2) := by
      simpa only [add_assoc, Int.reduceAdd] using period (n + 2)
    apply h
    by_cases he₀ : p n = 0 <;> by_cases he₁ : p (n + 1) = 0
    · exact ⟨n, rotated n he₀ he₁ (by omega) (by omega)⟩
    · refine ⟨n + 3, rotated _ (by omega) ?_ ?_ ?_⟩
      · simpa only [add_assoc, Int.reduceAdd, h₄] using he₀
      · simpa only [add_assoc, Int.reduceAdd, h₅] using (show p (n + 1) = 1 by omega)
      · simpa only [add_assoc, Int.reduceAdd, h₆] using
          (show p (n + 2) = 1 by omega)
    · refine ⟨n + 1, rotated _ he₁ ?_ ?_ ?_⟩ <;>
        simp only [add_assoc, Int.reduceAdd] <;> omega
    · refine ⟨n + 2, rotated _ (by omega) ?_ ?_ ?_⟩ <;>
        simp only [add_assoc, Int.reduceAdd] <;> omega

/-- **Difference-inverses of extraTribs.** Let $S$ be an extraTrib. There is exactly one
sequence $Q \colon \mathbb{Z} \to \mathbb{Q}$ that follows the Tribonacci rule
$Q(n+3) = Q(n+2) + Q(n+1) + Q(n)$ for all $n \in \mathbb{Z}$ and satisfies
$Q(n+1) - Q(n) = S(n)$ for all $n \in \mathbb{Z}$. Moreover, there is an extraTrib $Q$ with
$Q(n+1) - Q(n) = S(n)$ for all $n \in \mathbb{Z}$ if and only if $S$ is not of Type EEOO
(parities repeating even, even, odd, odd), that is, there is no integer $k$ such that for
every $n \in \mathbb{Z}$, $S(n)$ is even exactly when $(n - k) \bmod 4$ is $0$ or $1$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Theorem 9 (`jis-2025-25.5.4-thm-9`). -/
public theorem extraTrib_difference_inverse (S : ℤ → ℤ) (hS : IsExtraTrib S) :
    (∃! Q : ℤ → ℚ, (∀ n, Q (n + 3) = Q (n + 2) + Q (n + 1) + Q n) ∧
      ∀ n, Q (n + 1) - Q n = S n) ∧
    ((∃ Q : ℤ → ℤ, IsExtraTrib Q ∧ ∀ n, Q (n + 1) - Q n = S n) ↔
      ¬ ∃ k : ℤ, ∀ n, (Even (S n) ↔ (n - k) % 4 < 2)) := by
  obtain ⟨rec, N, hN⟩ := hS
  let D (n : ℤ) := S (n + 2) - S n
  have hrec (n : ℤ) : D (n + 3) = D (n + 2) + D (n + 1) + D n := by
    dsimp [D]
    rw [add_right_comm n 3 2, add_right_comm n 1 2]
    have := rec (n + 2)
    have := rec n
    omega
  have hdiff (n : ℤ) : D (n + 1) - D n = 2 * S n := by
    dsimp [D]
    rw [show n + 1 + 2 = n + 3 by omega]
    have := rec n
    omega
  let Q (n : ℤ) : ℚ := (D n : ℚ) / 2
  constructor
  · refine ⟨Q, ⟨?_, ?_⟩, ?_⟩
    · intro n
      simp only [Q, hrec n, Rat.intCast_add, add_div]
    · intro n
      simp only [Q, ← sub_div, ← Rat.intCast_sub, hdiff n, Rat.intCast_mul, Rat.intCast_ofNat]
      exact mul_div_cancel_left₀ _ (by decide)
    · rintro R ⟨hR, hΔ⟩
      funext n
      have h₂ := hΔ (n + 2)
      rw [show n + 2 + 1 = n + 3 by omega] at h₂
      simp only [Q, D, Rat.intCast_sub]
      linarith only [h₂, hΔ n, hR n]
  · rw [← extraTrib_parity_two_apart_iff rec]
    constructor
    · rintro ⟨R, hR, hΔ⟩ n
      have h₂ := hΔ (n + 2)
      rw [show n + 2 + 1 = n + 3 by omega] at h₂
      have h₀ := hΔ n
      have h₃ := hR.1 n
      omega
    · intro hp
      let R (n : ℤ) := D n / 2
      have hR (n : ℤ) : 2 * R n = D n := by
        have hd : (2 : ℤ) ∣ D n := by
          rw [Int.dvd_iff_emod_eq_zero]
          have := hp n
          dsimp [D]
          omega
        exact (mul_comm _ _).trans (Int.ediv_mul_cancel hd)
      refine ⟨R, ⟨?_, N + 1, ?_⟩, ?_⟩
      · intro n
        have h := hrec n
        simp only [← hR] at h
        omega
      · intro n hn
        have h := rec (n - 1)
        rw [show n - 1 + 3 = n + 2 by omega, show n - 1 + 2 = n + 1 by omega,
          show n - 1 + 1 = n by omega] at h
        have h₀ := hN (n - 1) (by omega)
        have h₁ := hN (n + 1) (by omega)
        have h₂ := hR n
        dsimp [D] at h₂
        omega
      · intro n
        have h := hdiff n
        simp only [← hR] at h
        omega

end MetaMathlibExt
