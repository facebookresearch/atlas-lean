/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ExtendedContinuant
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Tactic.Ring

/-!
# Silent-term formulas on table (33), case σ ≡ 1 (mod 6)

This module proves `silentTerms_table_one_mod_six`, the silent-term formulas on table (33)
for `σ ≡ 1 (mod 6)`.

Statements from Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73.
-/

namespace MetaMathlibExt

@[expose] public section

-- Reflect the order to turn the right-end recurrence into a left-end recurrence.
private theorem silentTerms_table_one_mod_six.leftRecurrence (x : ℤ → ℤ) (a b : ℤ) :
    extendedContinuant x a b =
      x b * extendedContinuant x (a - 1) (b + 1) + extendedContinuant x (a - 2) (b + 2) := by
  have reflect (j : ℤ) :
      extendedContinuant x (a - j) (b + j) =
        ((1 - a + j).negOnePow : ℤ) * extendedContinuant x (-a - 4 + j) (b + a + 2) := by
    convert extendedContinuant_neg_order x (b + j) (j - a) using 1 <;> ring_nf
  have r := extendedContinuant_recurrence x (-a - 2) (b + a + 2)
  have h₀ := reflect 0
  have h₁ := reflect 1
  have h₂ := reflect 2
  simp only [sub_zero, add_zero] at h₀
  rw [show 1 - a + 2 = (1 - a + 1) + 1 by ring, Int.negOnePow_succ, Int.negOnePow_succ,
    neg_neg] at h₂
  rw [Int.negOnePow_succ, Units.val_neg] at h₁
  rw [h₀, h₁, h₂]
  ring_nf at r ⊢
  rw [r]
  ring

set_option linter.unusedVariables false in
/-- **Silent-term formulas on table (33), case $\sigma \equiv 1 \pmod 6$.** Let $\sigma \ge 7$ be
an integer with $\sigma \equiv 1 \pmod 6$, let $c_1 \ne c_2$ be integers, and let
$x : \mathbb{Z} \to \mathbb{Z}$ be a bi-infinite integer sequence with $x_{-3} = x_0 + c_1$,
$x_{-2} = 1$, $x_{-1} = -1$ and, for all integers $4 \le m \le \sigma - 3$, $x_{-m} = -1$ if
$m \equiv 1 \pmod 3$ and $x_{-m} = 1$ otherwise. Write $K_a(x)_b$ for the extended continuant of
order $a$ with start index $b$, and put $z_0 = x_0 + c_2$ and
$w = -K_{\sigma-5}(x)_{-\sigma+3} - z_0 K_{\sigma-4}(x)_{-\sigma+3}$. Then $w \ne 0$ and
$-1 + K_{\sigma-6}(x)_{-\sigma+4} + z_0 K_{\sigma-5}(x)_{-\sigma+4} = w$.

So formula (29) of Theorem 7, with $z_0 = x_0 + c_2$, gives $x_{-\sigma+1} = w \ne 0$ and
$x_{-\sigma+2} = 1$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Proposition 3 (case `σ ≡ 1 mod 6`). -/
public theorem silentTerms_table_one_mod_six (x : ℤ → ℤ) (σ : ℤ) (hσ : σ % 6 = 1)
    (h7 : 7 ≤ σ) (c₁ c₂ : ℤ) (hc : c₁ ≠ c₂) (h3 : x (-3) = x 0 + c₁) (h2 : x (-2) = 1)
    (h1 : x (-1) = -1)
    (htab : ∀ m : ℤ, 4 ≤ m → m ≤ σ - 3 → x (-m) = if m % 3 = 1 then -1 else 1) :
    -extendedContinuant x (σ - 5) (-σ + 3) - (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3)
        ≠ 0 ∧
      -1 + extendedContinuant x (σ - 6) (-σ + 4) +
          (x 0 + c₂) * extendedContinuant x (σ - 5) (-σ + 4) =
        1 * (-extendedContinuant x (σ - 5) (-σ + 3) -
          (x 0 + c₂) * extendedContinuant x (σ - 4) (-σ + 3)) := by
  let z := x 0 + c₂
  let F (m : ℤ) := extendedContinuant x (m - 2) (-m) + z * extendedContinuant x (m - 1) (-m)
  have step (m : ℤ) : F m = x (-m) * F (m - 1) + F (m - 2) := by
    dsimp only [F]
    rw [silentTerms_table_one_mod_six.leftRecurrence x (m - 2) (-m),
      silentTerms_table_one_mod_six.leftRecurrence x (m - 1) (-m)]
    ring_nf
  have f₀ : F 0 = z := by
    simp [F, extendedContinuant_neg_two, extendedContinuant_neg_one]
  have f₁ : F 1 = 1 - z := by
    norm_num [F, extendedContinuant_neg_one, extendedContinuant_zero, h1]
    ring
  have f₂ : F 2 = 1 := by
    have h := step 2
    norm_num [h2, f₁, f₀] at h
    omega
  let t := 1 + c₁ - c₂
  have f₃ : F 3 = t := by
    have h := step 3
    norm_num [h3, f₂, f₁, z] at h
    dsimp [t]
    omega
  have table (m : ℤ) (hm : 4 ≤ m) (hle : m ≤ σ - 3) :
      F m = (if m % 3 = 1 then -1 else 1) * F (m - 1) + F (m - 2) := by
    rw [step m, htab m hm hle]
  -- Every six-term block of the table sends the pair (t, 1 - t) to itself.
  have rows (n : ℕ) (hn : 6 * (n : ℤ) + 4 ≤ σ - 3) :
      F (6 * n + 3) = t ∧ F (6 * n + 4) = 1 - t := by
    induction n with
    | zero =>
      have r := table 4 (by decide) (by omega)
      rw [ite_eq_left (show (4 : ℤ) % 3 = 1 by decide)] at r
      norm_num at r ⊢
      grind
    | succ n ih =>
      obtain ⟨p, q⟩ := ih (by omega)
      have r5 := table (6 * (n : ℤ) + 5) (by omega) (by omega)
      have r6 := table (6 * (n : ℤ) + 6) (by omega) (by omega)
      have r7 := table (6 * (n : ℤ) + 7) (by omega) (by omega)
      have r8 := table (6 * (n : ℤ) + 8) (by omega) (by omega)
      have r9 := table (6 * (n : ℤ) + 9) (by omega) (by omega)
      have r10 := table (6 * (n : ℤ) + 10) (by omega) (by omega)
      rw [ite_eq_right (show (6 * (n : ℤ) + 5) % 3 ≠ 1 by omega), one_mul] at r5
      rw [ite_eq_right (show (6 * (n : ℤ) + 6) % 3 ≠ 1 by omega), one_mul] at r6
      rw [ite_eq_left (show (6 * (n : ℤ) + 7) % 3 = 1 by omega), neg_one_mul] at r7
      rw [ite_eq_right (show (6 * (n : ℤ) + 8) % 3 ≠ 1 by omega), one_mul] at r8
      rw [ite_eq_right (show (6 * (n : ℤ) + 9) % 3 ≠ 1 by omega), one_mul] at r9
      rw [ite_eq_left (show (6 * (n : ℤ) + 10) % 3 = 1 by omega), neg_one_mul] at r10
      rw [show 6 * ((n + 1 : ℕ) : ℤ) + 3 = 6 * (n : ℤ) + 9 by simp only [Nat.cast_succ]; ring,
        show 6 * ((n + 1 : ℕ) : ℤ) + 4 = 6 * (n : ℤ) + 10 by simp only [Nat.cast_succ]; ring]
      grind
  obtain ⟨k, hk⟩ : ∃ k : ℕ, σ = 6 * (k : ℤ) + 7 := ⟨((σ - 7) / 6).toNat, by omega⟩
  obtain ⟨u, v⟩ := rows k (by omega)
  have hu : F (σ - 4) = t := by
    rw [show σ - 4 = 6 * (k : ℤ) + 3 by omega, u]
  have hv : F (σ - 3) = 1 - t := by
    rw [show σ - 3 = 6 * (k : ℤ) + 4 by omega, v]
  have hleft : -1 + F (σ - 4) = 1 * (-F (σ - 3)) := by
    rw [hu, hv]
    ring
  have hne : -F (σ - 3) ≠ 0 := by
    rw [hv]
    dsimp [t]
    omega
  dsimp only [F, z] at hleft hne
  constructor
  · convert hne using 1
    ring_nf
  · convert hleft using 1 <;> ring_nf

end

end MetaMathlibExt
