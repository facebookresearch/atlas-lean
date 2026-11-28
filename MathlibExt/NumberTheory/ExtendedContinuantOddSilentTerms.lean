/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ExtendedContinuant
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Terms of a σ-silent sequence for odd σ ≥ 5

For bi-infinite integer sequences `x y z : ℤ → ℤ`, `oddSilent_terms` shows that the
strict-equivalence hypotheses on the raw convergents force `xₙ = yₙ` for `n ≥ 0`, give explicit
formulas for `x_{-σ+1}` and `x_{-σ}` and for the product `x_{-σ+2} x_{-σ+1}` (the paper's
quotient formula for `x_{-σ+2}`, multiplied out), and force `x_{-n} = -z_{n-σ+1}` for
`n ≥ σ + 1`.

Statements from Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73.
-/

namespace MetaMathlibExt

@[expose] public section

-- Reflect the order to turn the right-end recurrence into a left-end recurrence.
private theorem oddSilent_leftRec (x : ℤ → ℤ) (a b : ℤ) :
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

-- East of the origin the difference of the two sequences kills both continuants in the
-- determinant identity, so the sequences agree.
private theorem oddSilent_east (x y : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1) :
    ∀ n : ℕ, x n = y n := by
  intro n
  rcases n with _ | _ | n
  · have h := (heast 0).1
    rw [show ((0 : ℕ) : ℤ) = 0 by omega, extendedContinuant_zero,
      extendedContinuant_zero] at h
    exact h
  · have h := (heast 1).2
    rw [show ((1 : ℕ) : ℤ) - 1 = 0 by omega, extendedContinuant_zero,
      extendedContinuant_zero] at h
    exact h
  · have eN := (heast (n + 2)).1
    have eNm1 := (heast (n + 1)).1
    have eNm2 := (heast n).1
    rw [show ((n + 1 : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) - 1 by omega] at eNm1
    rw [show ((n : ℕ) : ℤ) = ((n + 2 : ℕ) : ℤ) - 2 by omega] at eNm2
    have fN := (heast (n + 2)).2
    have fNm1 := (heast (n + 1)).2
    have fNm2 := (heast n).2
    rw [show ((n + 1 : ℕ) : ℤ) - 1 = ((n + 2 : ℕ) : ℤ) - 2 by omega] at fNm1
    rw [show ((n : ℕ) : ℤ) - 1 = ((n + 2 : ℕ) : ℤ) - 3 by omega] at fNm2
    have rx := extendedContinuant_recurrence x (((n + 2 : ℕ) : ℤ)) 0
    have ry := extendedContinuant_recurrence y (((n + 2 : ℕ) : ℤ)) 0
    rw [zero_add] at rx ry
    have rx1 := extendedContinuant_recurrence x (((n + 2 : ℕ) : ℤ) - 1) 1
    have ry1 := extendedContinuant_recurrence y (((n + 2 : ℕ) : ℤ) - 1) 1
    rw [show (1 : ℤ) + (((n + 2 : ℕ) : ℤ) - 1) = ((n + 2 : ℕ) : ℤ) by ring,
      show ((n + 2 : ℕ) : ℤ) - 1 - 1 = ((n + 2 : ℕ) : ℤ) - 2 by ring,
      show ((n + 2 : ℕ) : ℤ) - 1 - 2 = ((n + 2 : ℕ) : ℤ) - 3 by ring] at rx1 ry1
    have kill0 : (x (((n + 2 : ℕ) : ℤ)) - y (((n + 2 : ℕ) : ℤ))) *
        extendedContinuant x (((n + 2 : ℕ) : ℤ) - 1) 0 = 0 := by
      linear_combination -rx + ry + eN - eNm2 - (y (((n + 2 : ℕ) : ℤ))) * eNm1
    have kill1 : (x (((n + 2 : ℕ) : ℤ)) - y (((n + 2 : ℕ) : ℤ))) *
        extendedContinuant x (((n + 2 : ℕ) : ℤ) - 2) 1 = 0 := by
      linear_combination -rx1 + ry1 + fN - fNm2 - (y (((n + 2 : ℕ) : ℤ))) * fNm1
    have det := extendedContinuant_det x (((n + 2 : ℕ) : ℤ))
    have hds : (x (((n + 2 : ℕ) : ℤ)) - y (((n + 2 : ℕ) : ℤ))) *
        (extendedContinuant x (((n + 2 : ℕ) : ℤ)) 0 *
          extendedContinuant x (((n + 2 : ℕ) : ℤ) - 2) 1 -
          extendedContinuant x (((n + 2 : ℕ) : ℤ) - 1) 1 *
            extendedContinuant x (((n + 2 : ℕ) : ℤ) - 1) 0) = 0 := by
      linear_combination extendedContinuant x (((n + 2 : ℕ) : ℤ)) 0 * kill1 -
        extendedContinuant x (((n + 2 : ℕ) : ℤ) - 1) 1 * kill0
    rw [det] at hds
    have hxy : x (((n + 2 : ℕ) : ℤ)) - y (((n + 2 : ℕ) : ℤ)) = 0 :=
      (Units.mul_left_eq_zero _).mp hds
    exact sub_eq_zero.mp hxy

-- Far west of the origin the same determinant argument gives `x_{-n} = -z_{n-σ+1}`.
private theorem oddSilent_west_tail (x z : ℤ → ℤ) (σ : ℤ)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - σ - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - σ - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    ∀ n : ℤ, σ + 1 ≤ n → x (-n) = -z (n - σ + 1) := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = σ + 1 + j := ⟨(n - σ - 1).toNat, by omega⟩
  have e0 := (hwest j).1
  have e1 := (hwest (j + 1)).1
  have e2 := (hwest (j + 2)).1
  rw [show -((j : ℕ) : ℤ) - σ - 1 = -(σ + 1 + (j : ℤ)) by omega] at e0
  rw [show -(((j + 1 : ℕ) : ℤ)) - σ - 1 = -(σ + 1 + (j : ℤ)) - 1 by omega,
    show ((j + 1 : ℕ) : ℤ) = ((j + 2 : ℕ) : ℤ) - 1 by omega] at e1
  rw [show -(((j + 2 : ℕ) : ℤ)) - σ - 1 = -(σ + 1 + (j : ℤ)) - 2 by omega] at e2
  have f0 := (hwest j).2
  have f1 := (hwest (j + 1)).2
  have f2 := (hwest (j + 2)).2
  rw [show -((j : ℕ) : ℤ) - σ - 2 = -(σ + 1 + (j : ℤ)) - 1 by omega] at f0
  rw [show -(((j + 1 : ℕ) : ℤ)) - σ - 2 = -(σ + 1 + (j : ℤ)) - 2 by omega,
    show ((j + 1 : ℕ) : ℤ) - 1 = ((j + 2 : ℕ) : ℤ) - 2 by omega] at f1
  rw [show -(((j + 2 : ℕ) : ℤ)) - σ - 2 = -(σ + 1 + (j : ℤ)) - 3 by omega] at f2
  have rx := extendedContinuant_recurrence x (-(σ + 1 + (j : ℤ))) 0
  have rz := extendedContinuant_recurrence z (((j + 2 : ℕ) : ℤ)) 0
  rw [zero_add] at rx rz
  rw [show ((j + 2 : ℕ) : ℤ) - 2 = ((j : ℕ) : ℤ) by omega] at rz
  have rx1 := extendedContinuant_recurrence x (-(σ + 1 + (j : ℤ)) - 1) 1
  have rz1 := extendedContinuant_recurrence z (((j + 2 : ℕ) : ℤ) - 1) 1
  rw [show (1 : ℤ) + (-(σ + 1 + (j : ℤ)) - 1) = -(σ + 1 + (j : ℤ)) by ring,
    show -(σ + 1 + (j : ℤ)) - 1 - 1 = -(σ + 1 + (j : ℤ)) - 2 by ring,
    show -(σ + 1 + (j : ℤ)) - 1 - 2 = -(σ + 1 + (j : ℤ)) - 3 by ring] at rx1
  rw [show (1 : ℤ) + (((j + 2 : ℕ) : ℤ) - 1) = ((j + 2 : ℕ) : ℤ) by ring,
    show ((j + 2 : ℕ) : ℤ) - 1 - 1 = ((j + 2 : ℕ) : ℤ) - 2 by ring,
    show ((j + 2 : ℕ) : ℤ) - 1 - 2 = ((j : ℕ) : ℤ) - 1 by omega] at rz1
  have kill0 : (x (-(σ + 1 + (j : ℤ))) + z (((j + 2 : ℕ) : ℤ))) *
      extendedContinuant z (((j + 2 : ℕ) : ℤ) - 1) 0 = 0 := by
    linear_combination -rx + e0 - (x (-(σ + 1 + (j : ℤ)))) * e1 - e2 - rz
  have kill1 : (x (-(σ + 1 + (j : ℤ))) + z (((j + 2 : ℕ) : ℤ))) *
      extendedContinuant z (((j + 2 : ℕ) : ℤ) - 2) 1 = 0 := by
    linear_combination -rx1 + f0 - (x (-(σ + 1 + (j : ℤ)))) * f1 - f2 - rz1
  have det := extendedContinuant_det z (((j + 2 : ℕ) : ℤ))
  have hds : (x (-(σ + 1 + (j : ℤ))) + z (((j + 2 : ℕ) : ℤ))) *
      (extendedContinuant z (((j + 2 : ℕ) : ℤ)) 0 * extendedContinuant z (((j + 2 : ℕ) : ℤ) - 2) 1 -
        extendedContinuant z (((j + 2 : ℕ) : ℤ) - 1) 1 *
          extendedContinuant z (((j + 2 : ℕ) : ℤ) - 1) 0) = 0 := by
    linear_combination extendedContinuant z (((j + 2 : ℕ) : ℤ)) 0 * kill1 -
      extendedContinuant z (((j + 2 : ℕ) : ℤ) - 1) 1 * kill0
  rw [det] at hds
  have hadd : x (-(σ + 1 + (j : ℤ))) + z (((j + 2 : ℕ) : ℤ)) = 0 :=
    (Units.mul_left_eq_zero _).mp hds
  rw [show σ + 1 + (j : ℤ) - σ + 1 = ((j + 2 : ℕ) : ℤ) by omega]
  linear_combination hadd

-- The westbound hypotheses at `i = 0, 1` reflected to positive orders give the boundary terms.
private theorem oddSilent_boundary (x z : ℤ → ℤ) (σ : ℤ) (hσ : Odd σ)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - σ - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - σ - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    x (-σ + 2) * x (-σ + 1) = -1 + extendedContinuant x (σ - 6) (-σ + 4) +
        z 0 * extendedContinuant x (σ - 5) (-σ + 4) ∧
      x (-σ + 1) = -extendedContinuant x (σ - 5) (-σ + 3) -
        z 0 * extendedContinuant x (σ - 4) (-σ + 3) ∧
      x (-σ) = -extendedContinuant x (σ - 3) (-σ + 2) - z 1 := by
  obtain ⟨k, hk⟩ := hσ
  have hodd2 : Odd (σ + 2) := ⟨k + 1, by omega⟩
  have hev3 : Even (σ + 3) := ⟨k + 2, by omega⟩
  have hodd4 : Odd (σ + 4) := ⟨k + 2, by omega⟩
  have hs1 : ((((σ + 1) + 1)).negOnePow : ℤ) = -1 := by
    rw [show (σ + 1) + 1 = σ + 2 by ring]
    simp [Int.negOnePow_odd _ hodd2]
  have hs2 : ((((σ + 2) + 1)).negOnePow : ℤ) = 1 := by
    rw [show (σ + 2) + 1 = σ + 3 by ring]
    simp [Int.negOnePow_even _ hev3]
  have hs3 : ((((σ + 3) + 1)).negOnePow : ℤ) = -1 := by
    rw [show (σ + 3) + 1 = σ + 4 by ring]
    simp [Int.negOnePow_odd _ hodd4]
  have R1 : extendedContinuant x (-σ - 1) 0 = -extendedContinuant x (σ - 3) (-σ + 1) := by
    have h := extendedContinuant_neg_order x 0 (σ + 1)
    rw [hs1, show -(σ + 1) = -σ - 1 by ring,
      show σ + 1 - 4 = σ - 3 by ring, show 0 - (σ + 1) + 2 = -σ + 1 by ring] at h
    simpa using h
  have R2 : extendedContinuant x (-σ - 2) 1 = extendedContinuant x (σ - 2) (-σ + 1) := by
    have h := extendedContinuant_neg_order x 1 (σ + 2)
    rw [hs2, show -(σ + 2) = -σ - 2 by ring,
      show σ + 2 - 4 = σ - 2 by ring, show 1 - (σ + 2) + 2 = -σ + 1 by ring] at h
    simpa using h
  have R3 : extendedContinuant x (-σ - 2) 0 = extendedContinuant x (σ - 2) (-σ) := by
    have h := extendedContinuant_neg_order x 0 (σ + 2)
    rw [hs2, show -(σ + 2) = -σ - 2 by ring,
      show σ + 2 - 4 = σ - 2 by ring, show 0 - (σ + 2) + 2 = -σ by ring] at h
    simpa using h
  have R5 : extendedContinuant x (-σ - 3) 1 = -extendedContinuant x (σ - 1) (-σ) := by
    have h := extendedContinuant_neg_order x 1 (σ + 3)
    rw [hs3, show -(σ + 3) = -σ - 3 by ring,
      show σ + 3 - 4 = σ - 1 by ring, show 1 - (σ + 3) + 2 = -σ by ring] at h
    simpa using h
  have W0n : extendedContinuant x (-σ - 1) 0 = z 0 := by
    have h := (hwest 0).1
    rw [show -((0 : ℕ) : ℤ) - σ - 1 = -σ - 1 by omega,
      show ((0 : ℕ) : ℤ) = 0 by omega, extendedContinuant_zero] at h
    exact h
  have W0d : extendedContinuant x (-σ - 2) 1 = 1 := by
    have h := (hwest 0).2
    rw [show -((0 : ℕ) : ℤ) - σ - 2 = -σ - 2 by omega,
      show ((0 : ℕ) : ℤ) - 1 = -1 by omega, extendedContinuant_neg_one] at h
    exact h
  have W1n : extendedContinuant x (-σ - 2) 0 = z 1 * z 0 + 1 := by
    have h := (hwest 1).1
    rw [show -((1 : ℕ) : ℤ) - σ - 1 = -σ - 2 by omega, show ((1 : ℕ) : ℤ) = 1 by omega] at h
    have r := extendedContinuant_recurrence z 1 0
    rw [zero_add, show (1 : ℤ) - 1 = 0 by ring, show (1 : ℤ) - 2 = -1 by ring,
      extendedContinuant_zero, extendedContinuant_neg_one] at r
    rw [r] at h
    exact h
  have W1d : extendedContinuant x (-σ - 3) 1 = z 1 := by
    have h := (hwest 1).2
    rw [show -((1 : ℕ) : ℤ) - σ - 2 = -σ - 3 by omega,
      show ((1 : ℕ) : ℤ) - 1 = 0 by omega, extendedContinuant_zero] at h
    exact h
  have A : extendedContinuant x (σ - 3) (-σ + 1) = -z 0 := by linear_combination R1 - W0n
  have C : extendedContinuant x (σ - 2) (-σ + 1) = 1 := by linear_combination -R2 + W0d
  have B : extendedContinuant x (σ - 2) (-σ) = z 1 * z 0 + 1 := by
    linear_combination -R3 + W1n
  have E : extendedContinuant x (σ - 1) (-σ) = -z 1 := by linear_combination R5 - W1d
  have LA := oddSilent_leftRec x (σ - 3) (-σ + 1)
  rw [show σ - 3 - 1 = σ - 4 by ring, show -σ + 1 + 1 = -σ + 2 by ring,
    show σ - 3 - 2 = σ - 5 by ring, show -σ + 1 + 2 = -σ + 3 by ring] at LA
  have LC := oddSilent_leftRec x (σ - 2) (-σ + 1)
  rw [show σ - 2 - 1 = σ - 3 by ring, show -σ + 1 + 1 = -σ + 2 by ring,
    show σ - 2 - 2 = σ - 4 by ring, show -σ + 1 + 2 = -σ + 3 by ring] at LC
  have LB := oddSilent_leftRec x (σ - 2) (-σ)
  rw [show σ - 2 - 1 = σ - 3 by ring, show σ - 2 - 2 = σ - 4 by ring] at LB
  have LE := oddSilent_leftRec x (σ - 1) (-σ)
  rw [show σ - 1 - 1 = σ - 2 by ring, show σ - 1 - 2 = σ - 3 by ring] at LE
  have LH1 := oddSilent_leftRec x (σ - 4) (-σ + 2)
  rw [show σ - 4 - 1 = σ - 5 by ring, show -σ + 2 + 1 = -σ + 3 by ring,
    show σ - 4 - 2 = σ - 6 by ring, show -σ + 2 + 2 = -σ + 4 by ring] at LH1
  have LH2 := oddSilent_leftRec x (σ - 3) (-σ + 2)
  rw [show σ - 3 - 1 = σ - 4 by ring, show -σ + 2 + 1 = -σ + 3 by ring,
    show σ - 3 - 2 = σ - 5 by ring, show -σ + 2 + 2 = -σ + 4 by ring] at LH2
  have P4 : x (-σ) = -extendedContinuant x (σ - 3) (-σ + 2) - z 1 := by
    linear_combination -LE + E - (x (-σ)) * C
  have B2 : extendedContinuant x (σ - 4) (-σ + 2) =
      1 - z 0 * extendedContinuant x (σ - 3) (-σ + 2) := by
    linear_combination -LB + B - (x (-σ)) * A + (z 0) * P4
  have P3 : x (-σ + 1) = -extendedContinuant x (σ - 5) (-σ + 3) -
      z 0 * extendedContinuant x (σ - 4) (-σ + 3) := by
    linear_combination -LA + A - (z 0) * LC + (z 0) * C - (x (-σ + 1)) * B2
  have P2 : x (-σ + 2) * x (-σ + 1) = -1 + extendedContinuant x (σ - 6) (-σ + 4) +
      z 0 * extendedContinuant x (σ - 5) (-σ + 4) := by
    linear_combination LH1 + (z 0) * LH2 - B2 + (x (-σ + 2)) * P3
  exact ⟨P2, P3, P4⟩

set_option linter.unusedVariables false in
/-- **Terms of a $\sigma$-silent sequence for odd $\sigma \ge 5$.** Let $\sigma \ge 5$ be an odd
integer, let $x, y, z : \mathbb{Z} \to \mathbb{Z}$ be bi-infinite integer sequences, and write
$K_a(x)_b$ for the extended continuant of order $a$ with start index $b$. Suppose that for every
natural number $i$, $K_i(x)_0 = K_i(y)_0$, $K_{i-1}(x)_1 = K_{i-1}(y)_1$,
$K_{-i-\sigma-1}(x)_0 = K_i(z)_0$ and $K_{-i-\sigma-2}(x)_1 = K_{i-1}(z)_1$. Then $x_n = y_n$ for
every $n \ge 0$,
$x_{-\sigma+2} x_{-\sigma+1} = -1 + K_{\sigma-6}(x)_{-\sigma+4} + z_0 K_{\sigma-5}(x)_{-\sigma+4}$,
$x_{-\sigma+1} = -K_{\sigma-5}(x)_{-\sigma+3} - z_0 K_{\sigma-4}(x)_{-\sigma+3}$,
$x_{-\sigma} = -K_{\sigma-3}(x)_{-\sigma+2} - z_1$, and $x_{-n} = -z_{n-\sigma+1}$ for every integer
$n \ge \sigma + 1$.

The paper states the second formula as a quotient for $x_{-\sigma+2}$; here it is multiplied out.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 7. -/
public theorem oddSilent_terms (x y z : ℤ → ℤ) (σ : ℤ) (hσ : Odd σ) (h5 : 5 ≤ σ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - σ - 1) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - σ - 2) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    (∀ n : ℕ, x n = y n) ∧
      x (-σ + 2) * x (-σ + 1) = -1 + extendedContinuant x (σ - 6) (-σ + 4) +
        z 0 * extendedContinuant x (σ - 5) (-σ + 4) ∧
      x (-σ + 1) = -extendedContinuant x (σ - 5) (-σ + 3) -
        z 0 * extendedContinuant x (σ - 4) (-σ + 3) ∧
      x (-σ) = -extendedContinuant x (σ - 3) (-σ + 2) - z 1 ∧
      ∀ n : ℤ, σ + 1 ≤ n → x (-n) = -z (n - σ + 1) := by
  obtain ⟨p2, p3, p4⟩ := oddSilent_boundary x z σ hσ hwest
  exact ⟨oddSilent_east x y heast, p2, p3, p4, oddSilent_west_tail x z σ hwest⟩

end

end MetaMathlibExt
