/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Basic
import Mathlib.Order.Int.LeastGreatest

/-!
# Signs of an extraTrib to the left

An extraTrib obeys the Tribonacci recurrence on all integer indices and is eventually positive.
Three consecutive terms with the same strict sign force that sign at all later indices.
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

end MetaMathlibExt
