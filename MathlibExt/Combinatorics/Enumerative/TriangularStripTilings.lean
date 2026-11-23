/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

private lemma Qpos3 (Q : ℕ → ℕ) (hQ0 : Q 0 = 1) (hQ1 : Q 1 = 1) (hQ2 : Q 2 = 4)
    (hQrec : ∀ n : ℕ, 3 ≤ n →
      Q n = Q (n - 1) + 3 * Q (n - 2) + Q (n - 3)) :
    ∀ n : ℕ, 1 ≤ Q n ∧ 1 ≤ Q (n + 1) ∧ 1 ≤ Q (n + 2) := by
  intro n
  induction n with
  | zero =>
    simp only [zero_add]
    rw [hQ0, hQ1, hQ2]
    omega
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hrec := hQrec (n + 3) (by omega)
    have e1 : n + 3 - 1 = n + 2 := by omega
    have e2 : n + 3 - 2 = n + 1 := by omega
    have e3 : n + 3 - 3 = n := by omega
    rw [e1, e2, e3] at hrec
    have e4 : n + 1 + 2 = n + 3 := by omega
    rw [e4]
    refine ⟨h2, h3, ?_⟩
    omega

private lemma Qpos (Q : ℕ → ℕ) (hQ0 : Q 0 = 1) (hQ1 : Q 1 = 1) (hQ2 : Q 2 = 4)
    (hQrec : ∀ n : ℕ, 3 ≤ n →
      Q n = Q (n - 1) + 3 * Q (n - 2) + Q (n - 3)) (n : ℕ) : 1 ≤ Q n := by
  have h := Qpos3 Q hQ0 hQ1 hQ2 hQrec n
  exact h.1

private lemma Q3eq (Q : ℕ → ℕ) (hQ0 : Q 0 = 1) (hQ1 : Q 1 = 1) (hQ2 : Q 2 = 4)
    (hQrec : ∀ n : ℕ, 3 ≤ n →
      Q n = Q (n - 1) + 3 * Q (n - 2) + Q (n - 3)) : Q 3 = 8 := by
  have h := hQrec 3 (by omega)
  norm_num at h
  rw [hQ0, hQ1, hQ2] at h
  omega

private lemma sub_one_cast (Q : ℕ → ℕ) (npos : ∀ n : ℕ, 1 ≤ Q n) (n : ℕ) :
    ((2 * Q n - 1 : ℕ) : ℤ) = 2 * (Q n : ℤ) - 1 := by
  have h : 1 ≤ 2 * Q n := by
    have := npos n
    omega
  rw [Nat.cast_sub h]
  push_cast
  ring

private lemma Dall (Q : ℕ → ℕ) (hQ0 : Q 0 = 1) (hQ1 : Q 1 = 1) (hQ2 : Q 2 = 4)
    (hQrec : ∀ n : ℕ, 3 ≤ n →
      Q n = Q (n - 1) + 3 * Q (n - 2) + Q (n - 3)) :
    ∀ j : ℕ, 1 ≤ j →
      (12 * ((Q (2 * j) : ℤ)) ^ 2 - 2 * (Q (2 * j) : ℤ) * (Q (2 * j + 1) : ℤ) -
        2 * ((Q (2 * j + 1) : ℤ)) ^ 2 + 6 * (Q (2 * j - 1) : ℤ) * (Q (2 * j) : ℤ) +
        2 * (Q (2 * j - 1) : ℤ) * (Q (2 * j + 1) : ℤ) -
        2 * (Q (2 * j - 1) : ℤ) - 10 * (Q (2 * j) : ℤ) + 2 = 0) ∧
      (-4 * ((Q (2 * j - 1) : ℤ)) ^ 2 - 28 * ((Q (2 * j) : ℤ)) ^ 2 +
        6 * ((Q (2 * j + 1) : ℤ)) ^ 2 - 22 * (Q (2 * j - 1) : ℤ) * (Q (2 * j) : ℤ) -
        2 * (Q (2 * j - 1) : ℤ) * (Q (2 * j + 1) : ℤ) +
        2 * (Q (2 * j) : ℤ) * (Q (2 * j + 1) : ℤ) +
        6 * (Q (2 * j - 1) : ℤ) + 18 * (Q (2 * j) : ℤ) +
        4 * (Q (2 * j + 1) : ℤ) - 2 = 0) ∧
      (-4 * ((Q (2 * j) : ℤ)) ^ 2 - 2 * ((Q (2 * j + 1) : ℤ)) ^ 2 -
        2 * (Q (2 * j - 1) : ℤ) * (Q (2 * j) : ℤ) +
        2 * (Q (2 * j - 1) : ℤ) * (Q (2 * j + 1) : ℤ) +
        6 * (Q (2 * j) : ℤ) * (Q (2 * j + 1) : ℤ) +
        2 * (Q (2 * j - 1) : ℤ) + 6 * (Q (2 * j) : ℤ) -
        4 * (Q (2 * j + 1) : ℤ) - 2 = 0) := by
  have hQ3 : Q 3 = 8 := Q3eq Q hQ0 hQ1 hQ2 hQrec
  have base : (12 * ((Q (2 * 1) : ℤ)) ^ 2 - 2 * (Q (2 * 1) : ℤ) * (Q (2 * 1 + 1) : ℤ) -
        2 * ((Q (2 * 1 + 1) : ℤ)) ^ 2 + 6 * (Q (2 * 1 - 1) : ℤ) * (Q (2 * 1) : ℤ) +
        2 * (Q (2 * 1 - 1) : ℤ) * (Q (2 * 1 + 1) : ℤ) -
        2 * (Q (2 * 1 - 1) : ℤ) - 10 * (Q (2 * 1) : ℤ) + 2 = 0) ∧
      (-4 * ((Q (2 * 1 - 1) : ℤ)) ^ 2 - 28 * ((Q (2 * 1) : ℤ)) ^ 2 +
        6 * ((Q (2 * 1 + 1) : ℤ)) ^ 2 - 22 * (Q (2 * 1 - 1) : ℤ) * (Q (2 * 1) : ℤ) -
        2 * (Q (2 * 1 - 1) : ℤ) * (Q (2 * 1 + 1) : ℤ) +
        2 * (Q (2 * 1) : ℤ) * (Q (2 * 1 + 1) : ℤ) +
        6 * (Q (2 * 1 - 1) : ℤ) + 18 * (Q (2 * 1) : ℤ) +
        4 * (Q (2 * 1 + 1) : ℤ) - 2 = 0) ∧
      (-4 * ((Q (2 * 1) : ℤ)) ^ 2 - 2 * ((Q (2 * 1 + 1) : ℤ)) ^ 2 -
        2 * (Q (2 * 1 - 1) : ℤ) * (Q (2 * 1) : ℤ) +
        2 * (Q (2 * 1 - 1) : ℤ) * (Q (2 * 1 + 1) : ℤ) +
        6 * (Q (2 * 1) : ℤ) * (Q (2 * 1 + 1) : ℤ) +
        2 * (Q (2 * 1 - 1) : ℤ) + 6 * (Q (2 * 1) : ℤ) -
        4 * (Q (2 * 1 + 1) : ℤ) - 2 = 0) := by
    have e1 : 2 * 1 - 1 = 1 := by omega
    have e2 : 2 * 1 = 2 := by omega
    have e3 : 2 * 1 + 1 = 3 := by omega
    rw [e1, e2, e3, hQ1, hQ2, hQ3]
    norm_num
  have step : ∀ n : ℕ, 1 ≤ n →
      (12 * ((Q (2 * n) : ℤ)) ^ 2 - 2 * (Q (2 * n) : ℤ) * (Q (2 * n + 1) : ℤ) -
        2 * ((Q (2 * n + 1) : ℤ)) ^ 2 + 6 * (Q (2 * n - 1) : ℤ) * (Q (2 * n) : ℤ) +
        2 * (Q (2 * n - 1) : ℤ) * (Q (2 * n + 1) : ℤ) -
        2 * (Q (2 * n - 1) : ℤ) - 10 * (Q (2 * n) : ℤ) + 2 = 0) ∧
      (-4 * ((Q (2 * n - 1) : ℤ)) ^ 2 - 28 * ((Q (2 * n) : ℤ)) ^ 2 +
        6 * ((Q (2 * n + 1) : ℤ)) ^ 2 - 22 * (Q (2 * n - 1) : ℤ) * (Q (2 * n) : ℤ) -
        2 * (Q (2 * n - 1) : ℤ) * (Q (2 * n + 1) : ℤ) +
        2 * (Q (2 * n) : ℤ) * (Q (2 * n + 1) : ℤ) +
        6 * (Q (2 * n - 1) : ℤ) + 18 * (Q (2 * n) : ℤ) +
        4 * (Q (2 * n + 1) : ℤ) - 2 = 0) ∧
      (-4 * ((Q (2 * n) : ℤ)) ^ 2 - 2 * ((Q (2 * n + 1) : ℤ)) ^ 2 -
        2 * (Q (2 * n - 1) : ℤ) * (Q (2 * n) : ℤ) +
        2 * (Q (2 * n - 1) : ℤ) * (Q (2 * n + 1) : ℤ) +
        6 * (Q (2 * n) : ℤ) * (Q (2 * n + 1) : ℤ) +
        2 * (Q (2 * n - 1) : ℤ) + 6 * (Q (2 * n) : ℤ) -
        4 * (Q (2 * n + 1) : ℤ) - 2 = 0) →
      (12 * ((Q (2 * (n + 1)) : ℤ)) ^ 2 - 2 * (Q (2 * (n + 1)) : ℤ) * (Q (2 * (n + 1) + 1) : ℤ) -
        2 * ((Q (2 * (n + 1) + 1) : ℤ)) ^ 2 +
        6 * (Q (2 * (n + 1) - 1) : ℤ) * (Q (2 * (n + 1)) : ℤ) +
        2 * (Q (2 * (n + 1) - 1) : ℤ) * (Q (2 * (n + 1) + 1) : ℤ) -
        2 * (Q (2 * (n + 1) - 1) : ℤ) - 10 * (Q (2 * (n + 1)) : ℤ) + 2 = 0) ∧
      (-4 * ((Q (2 * (n + 1) - 1) : ℤ)) ^ 2 - 28 * ((Q (2 * (n + 1)) : ℤ)) ^ 2 +
        6 * ((Q (2 * (n + 1) + 1) : ℤ)) ^ 2 -
        22 * (Q (2 * (n + 1) - 1) : ℤ) * (Q (2 * (n + 1)) : ℤ) -
        2 * (Q (2 * (n + 1) - 1) : ℤ) * (Q (2 * (n + 1) + 1) : ℤ) +
        2 * (Q (2 * (n + 1)) : ℤ) * (Q (2 * (n + 1) + 1) : ℤ) +
        6 * (Q (2 * (n + 1) - 1) : ℤ) + 18 * (Q (2 * (n + 1)) : ℤ) +
        4 * (Q (2 * (n + 1) + 1) : ℤ) - 2 = 0) ∧
      (-4 * ((Q (2 * (n + 1)) : ℤ)) ^ 2 - 2 * ((Q (2 * (n + 1) + 1) : ℤ)) ^ 2 -
        2 * (Q (2 * (n + 1) - 1) : ℤ) * (Q (2 * (n + 1)) : ℤ) +
        2 * (Q (2 * (n + 1) - 1) : ℤ) * (Q (2 * (n + 1) + 1) : ℤ) +
        6 * (Q (2 * (n + 1)) : ℤ) * (Q (2 * (n + 1) + 1) : ℤ) +
        2 * (Q (2 * (n + 1) - 1) : ℤ) + 6 * (Q (2 * (n + 1)) : ℤ) -
        4 * (Q (2 * (n + 1) + 1) : ℤ) - 2 = 0) := by
    intro n hn ih
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hrw : (Q (2 * n + 2) : ℤ) =
        (Q (2 * n + 1) : ℤ) + 3 * (Q (2 * n) : ℤ) + (Q (2 * n - 1) : ℤ) := by
      have h := hQrec (2 * n + 2) (by omega)
      have e1 : 2 * n + 2 - 1 = 2 * n + 1 := by omega
      have e2 : 2 * n + 2 - 2 = 2 * n := by omega
      have e3 : 2 * n + 2 - 3 = 2 * n - 1 := by omega
      rw [e1, e2, e3] at h
      have hc : (Q (2 * n + 2) : ℤ) =
          ((Q (2 * n + 1) + 3 * Q (2 * n) + Q (2 * n - 1) : ℕ) : ℤ) := by
        rw [h]
      rw [hc]
      push_cast
      ring
    have hrw3 : (Q (2 * n + 3) : ℤ) =
        (Q (2 * n + 2) : ℤ) + 3 * (Q (2 * n + 1) : ℤ) + (Q (2 * n) : ℤ) := by
      have h := hQrec (2 * n + 3) (by omega)
      have e1 : 2 * n + 3 - 1 = 2 * n + 2 := by omega
      have e2 : 2 * n + 3 - 2 = 2 * n + 1 := by omega
      have e3 : 2 * n + 3 - 3 = 2 * n := by omega
      rw [e1, e2, e3] at h
      have hc : (Q (2 * n + 3) : ℤ) =
          ((Q (2 * n + 2) + 3 * Q (2 * n + 1) + Q (2 * n) : ℕ) : ℤ) := by
        rw [h]
      rw [hc]
      push_cast
      ring
    have g1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
    have g2 : 2 * (n + 1) = 2 * n + 2 := by omega
    have g3 : 2 * n + 2 + 1 = 2 * n + 3 := by omega
    rw [g1, g2, g3]
    rw [hrw, hrw3] at *
    refine ⟨?_, ?_, ?_⟩
    · linear_combination -2 * ih2 + ih3
    · linear_combination -1 * ih1 + 5 * ih2 - 5 * ih3
    · linear_combination 1 * ih1 + 2 * ih3
  have all : ∀ k : ℕ,
      (12 * ((Q (2 * (k + 1)) : ℤ)) ^ 2 - 2 * (Q (2 * (k + 1)) : ℤ) * (Q (2 * (k + 1) + 1) : ℤ) -
        2 * ((Q (2 * (k + 1) + 1) : ℤ)) ^ 2 +
        6 * (Q (2 * (k + 1) - 1) : ℤ) * (Q (2 * (k + 1)) : ℤ) +
        2 * (Q (2 * (k + 1) - 1) : ℤ) * (Q (2 * (k + 1) + 1) : ℤ) -
        2 * (Q (2 * (k + 1) - 1) : ℤ) - 10 * (Q (2 * (k + 1)) : ℤ) + 2 = 0) ∧
      (-4 * ((Q (2 * (k + 1) - 1) : ℤ)) ^ 2 - 28 * ((Q (2 * (k + 1)) : ℤ)) ^ 2 +
        6 * ((Q (2 * (k + 1) + 1) : ℤ)) ^ 2 -
        22 * (Q (2 * (k + 1) - 1) : ℤ) * (Q (2 * (k + 1)) : ℤ) -
        2 * (Q (2 * (k + 1) - 1) : ℤ) * (Q (2 * (k + 1) + 1) : ℤ) +
        2 * (Q (2 * (k + 1)) : ℤ) * (Q (2 * (k + 1) + 1) : ℤ) +
        6 * (Q (2 * (k + 1) - 1) : ℤ) + 18 * (Q (2 * (k + 1)) : ℤ) +
        4 * (Q (2 * (k + 1) + 1) : ℤ) - 2 = 0) ∧
      (-4 * ((Q (2 * (k + 1)) : ℤ)) ^ 2 - 2 * ((Q (2 * (k + 1) + 1) : ℤ)) ^ 2 -
        2 * (Q (2 * (k + 1) - 1) : ℤ) * (Q (2 * (k + 1)) : ℤ) +
        2 * (Q (2 * (k + 1) - 1) : ℤ) * (Q (2 * (k + 1) + 1) : ℤ) +
        6 * (Q (2 * (k + 1)) : ℤ) * (Q (2 * (k + 1) + 1) : ℤ) +
        2 * (Q (2 * (k + 1) - 1) : ℤ) + 6 * (Q (2 * (k + 1)) : ℤ) -
        4 * (Q (2 * (k + 1) + 1) : ℤ) - 2 = 0) := by
    intro k
    induction k with
    | zero => exact base
    | succ n ih => exact step (n + 1) (by omega) ih
  intro j hj
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact all k

/--
**Quarter-period factorizations of the triangular tiling numbers.** Let
$Q \colon \mathbb{N} \to \mathbb{N}$ satisfy $Q(0) = Q(1) = 1$, $Q(2) = 4$ and
$Q(n) = Q(n-1) + 3Q(n-2) + Q(n-3)$ for every $n \ge 3$. Then for every $m \ge 1$,
$$Q(4m) = (2Q(2m-1) + 1)(2Q(2m) - 1),$$
$$Q(4m+1) = (2Q(2m) - 1)^2,$$
$$Q(4m+2) = 2(Q(2m-1) + Q(2m))(Q(2m) + Q(2m+1)),$$
$$Q(4m+3) = 2(Q(2m) + Q(2m+1))^2.$$

All values of $Q$ are at least $1$, so the subtractions above are exact. In the source, $Q(n)$ is
the number of tilings of a triangular strip.

Proves `Wanted` entry `quarter_period_factorizations`.

Source: Mark Shattuck, "Combinatorial Proofs of Some Formulas for Triangular
Tilings," Journal of Integer Sequences 17 (2014), Article 14.5.5,
Theorem (label thm2, due to Bodeen et al.), lines 103–112,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Shattuck/shattuck8.tex

Source: the recurrence and initial values are equation (rec) at lines 122–125.
-/
theorem quarter_period_factorizations
    (Q : ℕ → ℕ)
    (hQ0 : Q 0 = 1)
    (hQ1 : Q 1 = 1)
    (hQ2 : Q 2 = 4)
    (hQrec : ∀ n : ℕ, 3 ≤ n →
      Q n = Q (n - 1) + 3 * Q (n - 2) + Q (n - 3))
    (m : ℕ)
    (hm : 1 ≤ m) :
    Q (4 * m) =
        (2 * Q (2 * m - 1) + 1) * (2 * Q (2 * m) - 1) ∧
      Q (4 * m + 1) = (2 * Q (2 * m) - 1) ^ 2 ∧
      Q (4 * m + 2) =
        2 * (Q (2 * m - 1) + Q (2 * m)) *
          (Q (2 * m) + Q (2 * m + 1)) ∧
      Q (4 * m + 3) =
        2 * (Q (2 * m) + Q (2 * m + 1)) ^ 2 := by
  have npos : ∀ n : ℕ, 1 ≤ Q n := Qpos Q hQ0 hQ1 hQ2 hQrec
  have hQ3 : Q 3 = 8 := Q3eq Q hQ0 hQ1 hQ2 hQrec
  have hQ4 : Q 4 = 21 := by
    have h := hQrec 4 (by omega)
    norm_num at h
    rw [hQ3, hQ2, hQ1] at h
    omega
  have hQ5 : Q 5 = 49 := by
    have h := hQrec 5 (by omega)
    norm_num at h
    rw [hQ4, hQ3, hQ2] at h
    omega
  have hQ6 : Q 6 = 120 := by
    have h := hQrec 6 (by omega)
    norm_num at h
    rw [hQ5, hQ4, hQ3] at h
    omega
  have hQ7 : Q 7 = 288 := by
    have h := hQrec 7 (by omega)
    norm_num at h
    rw [hQ6, hQ5, hQ4] at h
    omega
  have hdall := Dall Q hQ0 hQ1 hQ2 hQrec
  have base : Q (4 * 1) = (2 * Q (2 * 1 - 1) + 1) * (2 * Q (2 * 1) - 1) ∧
      Q (4 * 1 + 1) = (2 * Q (2 * 1) - 1) ^ 2 ∧
      Q (4 * 1 + 2) = 2 * (Q (2 * 1 - 1) + Q (2 * 1)) * (Q (2 * 1) + Q (2 * 1 + 1)) ∧
      Q (4 * 1 + 3) = 2 * (Q (2 * 1) + Q (2 * 1 + 1)) ^ 2 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change Q 4 = (2 * Q 1 + 1) * (2 * Q 2 - 1)
      rw [hQ4, hQ1, hQ2]
    · change Q 5 = (2 * Q 2 - 1) ^ 2
      rw [hQ5, hQ2]
      decide
    · change Q 6 = 2 * (Q 1 + Q 2) * (Q 2 + Q 3)
      rw [hQ6, hQ1, hQ2, hQ3]
    · change Q 7 = 2 * (Q 2 + Q 3) ^ 2
      rw [hQ7, hQ2, hQ3]
      decide
  have step : ∀ k : ℕ, 1 ≤ k →
      (Q (4 * k) = (2 * Q (2 * k - 1) + 1) * (2 * Q (2 * k) - 1) ∧
      Q (4 * k + 1) = (2 * Q (2 * k) - 1) ^ 2 ∧
      Q (4 * k + 2) = 2 * (Q (2 * k - 1) + Q (2 * k)) * (Q (2 * k) + Q (2 * k + 1)) ∧
      Q (4 * k + 3) = 2 * (Q (2 * k) + Q (2 * k + 1)) ^ 2) →
      (Q (4 * (k + 1)) = (2 * Q (2 * (k + 1) - 1) + 1) * (2 * Q (2 * (k + 1)) - 1) ∧
      Q (4 * (k + 1) + 1) = (2 * Q (2 * (k + 1)) - 1) ^ 2 ∧
      Q (4 * (k + 1) + 2) = 2 * (Q (2 * (k + 1) - 1) + Q (2 * (k + 1))) *
        (Q (2 * (k + 1)) + Q (2 * (k + 1) + 1)) ∧
      Q (4 * (k + 1) + 3) = 2 * (Q (2 * (k + 1)) + Q (2 * (k + 1) + 1)) ^ 2) := by
    intro k hk ih
    obtain ⟨ih0, ih1, ih2, ih3⟩ := ih
    obtain ⟨D1, D2, D3⟩ := hdall k hk
    have rV0 : Q (4 * k + 4) = Q (4 * k + 3) + 3 * Q (4 * k + 2) + Q (4 * k + 1) := by
      have h := hQrec (4 * k + 4) (by omega)
      have e1 : 4 * k + 4 - 1 = 4 * k + 3 := by omega
      have e2 : 4 * k + 4 - 2 = 4 * k + 2 := by omega
      have e3 : 4 * k + 4 - 3 = 4 * k + 1 := by omega
      rw [e1, e2, e3] at h
      exact h
    have rV1 : Q (4 * k + 5) = Q (4 * k + 4) + 3 * Q (4 * k + 3) + Q (4 * k + 2) := by
      have h := hQrec (4 * k + 5) (by omega)
      have e1 : 4 * k + 5 - 1 = 4 * k + 4 := by omega
      have e2 : 4 * k + 5 - 2 = 4 * k + 3 := by omega
      have e3 : 4 * k + 5 - 3 = 4 * k + 2 := by omega
      rw [e1, e2, e3] at h
      exact h
    have rV2 : Q (4 * k + 6) = Q (4 * k + 5) + 3 * Q (4 * k + 4) + Q (4 * k + 3) := by
      have h := hQrec (4 * k + 6) (by omega)
      have e1 : 4 * k + 6 - 1 = 4 * k + 5 := by omega
      have e2 : 4 * k + 6 - 2 = 4 * k + 4 := by omega
      have e3 : 4 * k + 6 - 3 = 4 * k + 3 := by omega
      rw [e1, e2, e3] at h
      exact h
    have rV3 : Q (4 * k + 7) = Q (4 * k + 6) + 3 * Q (4 * k + 5) + Q (4 * k + 4) := by
      have h := hQrec (4 * k + 7) (by omega)
      have e1 : 4 * k + 7 - 1 = 4 * k + 6 := by omega
      have e2 : 4 * k + 7 - 2 = 4 * k + 5 := by omega
      have e3 : 4 * k + 7 - 3 = 4 * k + 4 := by omega
      rw [e1, e2, e3] at h
      exact h
    have rd : Q (2 * k + 2) = Q (2 * k + 1) + 3 * Q (2 * k) + Q (2 * k - 1) := by
      have h := hQrec (2 * k + 2) (by omega)
      have e1 : 2 * k + 2 - 1 = 2 * k + 1 := by omega
      have e2 : 2 * k + 2 - 2 = 2 * k := by omega
      have e3 : 2 * k + 2 - 3 = 2 * k - 1 := by omega
      rw [e1, e2, e3] at h
      exact h
    have re : Q (2 * k + 3) = Q (2 * k + 2) + 3 * Q (2 * k + 1) + Q (2 * k) := by
      have h := hQrec (2 * k + 3) (by omega)
      have e1 : 2 * k + 3 - 1 = 2 * k + 2 := by omega
      have e2 : 2 * k + 3 - 2 = 2 * k + 1 := by omega
      have e3 : 2 * k + 3 - 3 = 2 * k := by omega
      rw [e1, e2, e3] at h
      exact h
    have rV0Z : (Q (4 * k + 4) : ℤ) =
        (Q (4 * k + 3) : ℤ) + 3 * (Q (4 * k + 2) : ℤ) + (Q (4 * k + 1) : ℤ) := by
      exact_mod_cast rV0
    have rV1Z : (Q (4 * k + 5) : ℤ) =
        (Q (4 * k + 4) : ℤ) + 3 * (Q (4 * k + 3) : ℤ) + (Q (4 * k + 2) : ℤ) := by
      exact_mod_cast rV1
    have rV2Z : (Q (4 * k + 6) : ℤ) =
        (Q (4 * k + 5) : ℤ) + 3 * (Q (4 * k + 4) : ℤ) + (Q (4 * k + 3) : ℤ) := by
      exact_mod_cast rV2
    have rV3Z : (Q (4 * k + 7) : ℤ) =
        (Q (4 * k + 6) : ℤ) + 3 * (Q (4 * k + 5) : ℤ) + (Q (4 * k + 4) : ℤ) := by
      exact_mod_cast rV3
    have hdZ : (Q (2 * k + 2) : ℤ) =
        (Q (2 * k + 1) : ℤ) + 3 * (Q (2 * k) : ℤ) + (Q (2 * k - 1) : ℤ) := by
      exact_mod_cast rd
    have heZ : (Q (2 * k + 3) : ℤ) =
        (Q (2 * k + 2) : ℤ) + 3 * (Q (2 * k + 1) : ℤ) + (Q (2 * k) : ℤ) := by
      exact_mod_cast re
    have hsub : ((2 * Q (2 * k + 2) - 1 : ℕ) : ℤ) = 2 * (Q (2 * k + 2) : ℤ) - 1 :=
      sub_one_cast Q npos (2 * k + 2)
    have e1Z : (Q (4 * k + 1) : ℤ) = (2 * (Q (2 * k) : ℤ) - 1) ^ 2 := by
      calc (Q (4 * k + 1) : ℤ) = ((((2 * Q (2 * k) - 1) ^ 2 : ℕ)) : ℤ) := by rw [ih1]
        _ = (((2 * Q (2 * k) - 1 : ℕ)) : ℤ) ^ 2 := by push_cast; ring
        _ = (2 * (Q (2 * k) : ℤ) - 1) ^ 2 := by
          have hs : ((2 * Q (2 * k) - 1 : ℕ) : ℤ) = 2 * (Q (2 * k) : ℤ) - 1 :=
            sub_one_cast Q npos (2 * k)
          rw [hs]
    have e2Z : (Q (4 * k + 2) : ℤ) =
        2 * ((Q (2 * k - 1) : ℤ) + (Q (2 * k) : ℤ)) * ((Q (2 * k) : ℤ) + (Q (2 * k + 1) : ℤ)) := by
      have hc : (Q (4 * k + 2) : ℤ) =
          (((2 * (Q (2 * k - 1) + Q (2 * k)) * (Q (2 * k) + Q (2 * k + 1)) : ℕ)) : ℤ) := by
        rw [ih2]
      rw [hc]
      push_cast
      ring
    have e3Z : (Q (4 * k + 3) : ℤ) =
        2 * ((Q (2 * k) : ℤ) + (Q (2 * k + 1) : ℤ)) ^ 2 := by
      have hc : (Q (4 * k + 3) : ℤ) =
          (((2 * (Q (2 * k) + Q (2 * k + 1)) ^ 2 : ℕ)) : ℤ) := by
        rw [ih3]
      rw [hc]
      push_cast
      ring
    have g0Z : (Q (4 * k + 4) : ℤ) =
        (2 * (Q (2 * k + 1) : ℤ) + 1) * (2 * (Q (2 * k + 2) : ℤ) - 1) := by
      rw [rV0Z, e1Z, e2Z, e3Z, hdZ]
      linear_combination D1
    have g0 : Q (4 * k + 4) = (2 * Q (2 * k + 1) + 1) * (2 * Q (2 * k + 2) - 1) := by
      have cast0 : ((((2 * Q (2 * k + 1) + 1) * (2 * Q (2 * k + 2) - 1) : ℕ)) : ℤ) =
          (2 * (Q (2 * k + 1) : ℤ) + 1) * (2 * (Q (2 * k + 2) : ℤ) - 1) := by
        calc ((((2 * Q (2 * k + 1) + 1) * (2 * Q (2 * k + 2) - 1) : ℕ)) : ℤ)
            = (((2 * Q (2 * k + 1) + 1 : ℕ)) : ℤ) * (((2 * Q (2 * k + 2) - 1 : ℕ)) : ℤ) := by
              push_cast; ring
          _ = (2 * (Q (2 * k + 1) : ℤ) + 1) * (2 * (Q (2 * k + 2) : ℤ) - 1) := by
              rw [hsub]; push_cast; ring
      have hcast : (Q (4 * k + 4) : ℤ) =
          ((((2 * Q (2 * k + 1) + 1) * (2 * Q (2 * k + 2) - 1) : ℕ)) : ℤ) := by
        rw [cast0]
        exact g0Z
      exact_mod_cast hcast
    have g1Z : (Q (4 * k + 5) : ℤ) = (2 * (Q (2 * k + 2) : ℤ) - 1) ^ 2 := by
      rw [rV1Z, g0Z, e3Z, e2Z, hdZ]
      linear_combination D2
    have g1 : Q (4 * k + 5) = (2 * Q (2 * k + 2) - 1) ^ 2 := by
      have cast1 : (((((2 * Q (2 * k + 2) - 1) ^ 2 : ℕ))) : ℤ) =
          (2 * (Q (2 * k + 2) : ℤ) - 1) ^ 2 := by
        calc (((((2 * Q (2 * k + 2) - 1) ^ 2 : ℕ))) : ℤ)
            = (((2 * Q (2 * k + 2) - 1 : ℕ)) : ℤ) ^ 2 := by push_cast; ring
          _ = (2 * (Q (2 * k + 2) : ℤ) - 1) ^ 2 := by rw [hsub]
      have hcast : (Q (4 * k + 5) : ℤ) = (((((2 * Q (2 * k + 2) - 1) ^ 2 : ℕ))) : ℤ) := by
        rw [cast1]
        exact g1Z
      exact_mod_cast hcast
    have g2Z : (Q (4 * k + 6) : ℤ) =
        2 * ((Q (2 * k + 1) : ℤ) + (Q (2 * k + 2) : ℤ)) *
          ((Q (2 * k + 2) : ℤ) + (Q (2 * k + 3) : ℤ)) := by
      rw [rV2Z, g1Z, g0Z, e3Z, heZ, hdZ]
      linear_combination D3
    have g2 : Q (4 * k + 6) =
        2 * (Q (2 * k + 1) + Q (2 * k + 2)) * (Q (2 * k + 2) + Q (2 * k + 3)) := by
      have hcast : (Q (4 * k + 6) : ℤ) =
          (((2 * (Q (2 * k + 1) + Q (2 * k + 2)) * (Q (2 * k + 2) + Q (2 * k + 3)) : ℕ)) : ℤ) := by
        have c : (((2 * (Q (2 * k + 1) + Q (2 * k + 2)) *
            (Q (2 * k + 2) + Q (2 * k + 3)) : ℕ)) : ℤ) =
            2 * ((Q (2 * k + 1) : ℤ) + (Q (2 * k + 2) : ℤ)) *
              ((Q (2 * k + 2) : ℤ) + (Q (2 * k + 3) : ℤ)) := by
          push_cast; ring
        rw [c]
        exact g2Z
      exact_mod_cast hcast
    have g3Z : (Q (4 * k + 7) : ℤ) =
        2 * ((Q (2 * k + 2) : ℤ) + (Q (2 * k + 3) : ℤ)) ^ 2 := by
      rw [rV3Z, g2Z, g1Z, g0Z, heZ, hdZ]
      linear_combination -2 * D2 + D3
    have g3 : Q (4 * k + 7) = 2 * (Q (2 * k + 2) + Q (2 * k + 3)) ^ 2 := by
      have hcast : (Q (4 * k + 7) : ℤ) =
          (((2 * (Q (2 * k + 2) + Q (2 * k + 3)) ^ 2 : ℕ)) : ℤ) := by
        have c : (((2 * (Q (2 * k + 2) + Q (2 * k + 3)) ^ 2 : ℕ)) : ℤ) =
            2 * ((Q (2 * k + 2) : ℤ) + (Q (2 * k + 3) : ℤ)) ^ 2 := by
          push_cast; ring
        rw [c]
        exact g3Z
      exact_mod_cast hcast
    have iV0 : 4 * (k + 1) = 4 * k + 4 := by omega
    have iV1 : 4 * (k + 1) + 1 = 4 * k + 5 := by omega
    have iV2 : 4 * (k + 1) + 2 = 4 * k + 6 := by omega
    have iV3 : 4 * (k + 1) + 3 = 4 * k + 7 := by omega
    have ic : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    have id_ : 2 * (k + 1) = 2 * k + 2 := by omega
    have ie : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [iV0, ic, id_]
      exact g0
    · rw [iV1, id_]
      exact g1
    · rw [iV2, ic, ie, id_]
      exact g2
    · rw [iV3, ie, id_]
      exact g3
  have all : ∀ t : ℕ,
      (Q (4 * (t + 1)) = (2 * Q (2 * (t + 1) - 1) + 1) * (2 * Q (2 * (t + 1)) - 1) ∧
      Q (4 * (t + 1) + 1) = (2 * Q (2 * (t + 1)) - 1) ^ 2 ∧
      Q (4 * (t + 1) + 2) = 2 * (Q (2 * (t + 1) - 1) + Q (2 * (t + 1))) *
        (Q (2 * (t + 1)) + Q (2 * (t + 1) + 1)) ∧
      Q (4 * (t + 1) + 3) = 2 * (Q (2 * (t + 1)) + Q (2 * (t + 1) + 1)) ^ 2) := by
    intro t
    induction t with
    | zero => exact base
    | succ n ih => exact step (n + 1) (by omega) ih
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact all k


end MetaMathlibExt
