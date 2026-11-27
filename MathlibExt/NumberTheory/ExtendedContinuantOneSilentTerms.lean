/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ExtendedContinuant
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Terms of a $1$-silent sequence

If the raw convergents of a bi-infinite integer sequence `x` agree strictly with those of `y`
eastbound and with those of `z` westbound, then `x` and `y` agree on every nonnegative index,
`x (-n) = -z n` for every `n ≥ 1`, and `z 0 = 0` (`oneSilent_terms`).

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A factor annihilating both entries of a `±1` determinant is zero. -/
private theorem oneSilent_terms.detEqZero (d A B C D : ℤ) (k : ℤ)
    (h1 : d * A = 0) (h2 : d * B = 0)
    (hdet : A * C - B * D = (k.negOnePow : ℤ)) : d = 0 := by
  have hs : (k.negOnePow : ℤ) ≠ 0 := by
    rcases Int.units_eq_one_or k.negOnePow with h | h <;> rw [h] <;> simp
  have h0 : d * (k.negOnePow : ℤ) = 0 := by
    rw [← hdet]
    linear_combination C * h1 - D * h2
  exact (mul_eq_zero.mp h0).resolve_right hs

/-- Agreement of eastbound continuants at orders `m - 1` through `m + 2` gives
`x (m + 2) = y (m + 2)`. -/
private theorem oneSilent_terms.eastStep (x y : ℤ → ℤ) (m : ℤ)
    (hN : extendedContinuant x (m + 2) 0 = extendedContinuant y (m + 2) 0)
    (hN' : extendedContinuant x (m + 1) 1 = extendedContinuant y (m + 1) 1)
    (h1 : extendedContinuant x (m + 1) 0 = extendedContinuant y (m + 1) 0)
    (h1' : extendedContinuant x m 1 = extendedContinuant y m 1)
    (h0 : extendedContinuant x m 0 = extendedContinuant y m 0)
    (h0' : extendedContinuant x (m - 1) 1 = extendedContinuant y (m - 1) 1) :
    x (m + 2) = y (m + 2) := by
  have rx := extendedContinuant_recurrence x (m + 2) 0
  have ry := extendedContinuant_recurrence y (m + 2) 0
  have rx' := extendedContinuant_recurrence x (m + 1) 1
  have ry' := extendedContinuant_recurrence y (m + 1) 1
  rw [show (0 : ℤ) + (m + 2) = m + 2 by omega, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] at rx ry
  rw [show (1 : ℤ) + (m + 1) = m + 2 by omega, show m + 1 - 1 = m by omega,
    show m + 1 - 2 = m - 1 by omega] at rx' ry'
  have e1 : (x (m + 2) - y (m + 2)) * extendedContinuant x (m + 1) 0 = 0 := by
    linear_combination hN - rx + ry - h0 - y (m + 2) * h1
  have e2 : (x (m + 2) - y (m + 2)) * extendedContinuant x m 1 = 0 := by
    linear_combination hN' - rx' + ry' - h0' - y (m + 2) * h1'
  have hdet := extendedContinuant_det x (m + 1)
  rw [show m + 1 - 2 = m - 1 by omega, show m + 1 - 1 = m by omega] at hdet
  have hzero : x (m + 2) - y (m + 2) = 0 :=
    oneSilent_terms.detEqZero _ _ _ _ _ _ e1 e2 hdet
  exact sub_eq_zero.mp hzero

/-- Agreement of westbound continuants at orders `-m - 5` through `-m - 2` gives
`x (-m - 2) = -z (m + 2)`. -/
private theorem oneSilent_terms.westStep (x z : ℤ → ℤ) (m : ℤ)
    (wN : extendedContinuant x (-m - 4) 0 = extendedContinuant z (m + 2) 0)
    (wN' : extendedContinuant x (-m - 5) 1 = extendedContinuant z (m + 1) 1)
    (w1 : extendedContinuant x (-m - 3) 0 = extendedContinuant z (m + 1) 0)
    (w1' : extendedContinuant x (-m - 4) 1 = extendedContinuant z m 1)
    (w0 : extendedContinuant x (-m - 2) 0 = extendedContinuant z m 0)
    (w0' : extendedContinuant x (-m - 3) 1 = extendedContinuant z (m - 1) 1) :
    x (-m - 2) = -z (m + 2) := by
  have rx := extendedContinuant_recurrence x (-m - 2) 0
  have rz := extendedContinuant_recurrence z (m + 2) 0
  have rx' := extendedContinuant_recurrence x (-m - 3) 1
  have rz' := extendedContinuant_recurrence z (m + 1) 1
  rw [show (0 : ℤ) + (-m - 2) = -m - 2 by omega, show -m - 2 - 1 = -m - 3 by omega,
    show -m - 2 - 2 = -m - 4 by omega] at rx
  rw [show (0 : ℤ) + (m + 2) = m + 2 by omega, show m + 2 - 1 = m + 1 by omega,
    show m + 2 - 2 = m by omega] at rz
  rw [show (1 : ℤ) + (-m - 3) = -m - 2 by omega, show -m - 3 - 1 = -m - 4 by omega,
    show -m - 3 - 2 = -m - 5 by omega] at rx'
  rw [show (1 : ℤ) + (m + 1) = m + 2 by omega, show m + 1 - 1 = m by omega,
    show m + 1 - 2 = m - 1 by omega] at rz'
  have e1 : (x (-m - 2) + z (m + 2)) * extendedContinuant z (m + 1) 0 = 0 := by
    linear_combination -rx + w0 - wN - rz - x (-m - 2) * w1
  have e2 : (x (-m - 2) + z (m + 2)) * extendedContinuant z m 1 = 0 := by
    linear_combination -rx' + w0' - wN' - rz' - x (-m - 2) * w1'
  have hdet := extendedContinuant_det z (m + 1)
  rw [show m + 1 - 2 = m - 1 by omega, show m + 1 - 1 = m by omega] at hdet
  have hzero : x (-m - 2) + z (m + 2) = 0 :=
    oneSilent_terms.detEqZero _ _ _ _ _ _ e1 e2 hdet
  exact eq_neg_iff_add_eq_zero.mpr hzero

/-- **Terms of a $1$-silent sequence.** Let $x, y, z : \mathbb{Z} \to \mathbb{Z}$ be bi-infinite
integer sequences and write $K_a(x)_b$ for the extended continuant of order $a$ with start index
$b$. Suppose that for every natural number $i$, $K_i(x)_0 = K_i(y)_0$,
$K_{i-1}(x)_1 = K_{i-1}(y)_1$, $K_{-i-2}(x)_0 = K_i(z)_0$ and $K_{-i-3}(x)_1 = K_{i-1}(z)_1$.
Then $x_n = y_n$ for every $n \ge 0$, $x_{-n} = -z_n$ for every $n \ge 1$, and $z_0 = 0$.

In the paper's terms the hypotheses say that the raw convergents $k_i = K_i(x)_0 / K_{i-1}(x)_1$
of $x$ are strictly equivalent (equal numerators and equal denominators) to the raw convergents
$c_i$ of $y$, and $k_{-i-2}$ to the raw convergents $d_i$ of $z$, for all $i \ge 0$. The
conclusion $z_0 = 0$ matches the paper's $0 < \bar\alpha < 1$ for the EA-generated SCF of the
irrational $\bar\alpha$.

Source: Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued Fractions*,
INTEGERS 26 (2026), Article A73, Theorem 5. -/
public theorem oneSilent_terms (x y z : ℤ → ℤ)
    (heast : ∀ i : ℕ, extendedContinuant x i 0 = extendedContinuant y i 0 ∧
      extendedContinuant x ((i : ℤ) - 1) 1 = extendedContinuant y ((i : ℤ) - 1) 1)
    (hwest : ∀ i : ℕ, extendedContinuant x (-(i : ℤ) - 2) 0 = extendedContinuant z i 0 ∧
      extendedContinuant x (-(i : ℤ) - 3) 1 = extendedContinuant z ((i : ℤ) - 1) 1) :
    (∀ n : ℕ, x n = y n) ∧ (∀ n : ℕ, 1 ≤ n → x (-(n : ℤ)) = -z n) ∧ z 0 = 0 := by
  have east : ∀ n : ℕ, x n = y n := by
    intro n
    match n with
    | 0 => simpa [extendedContinuant_zero] using (heast 0).1
    | 1 => simpa [extendedContinuant_zero] using (heast 1).2
    | j + 2 =>
      have eN : ((j + 2 : ℕ) : ℤ) = (j : ℤ) + 2 := by omega
      have eM : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by omega
      have dN : ((j + 2 : ℕ) : ℤ) - 1 = (j : ℤ) + 1 := by omega
      have dM : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      have hN := (heast (j + 2)).1
      have hN' := (heast (j + 2)).2
      have h1 := (heast (j + 1)).1
      have h1' := (heast (j + 1)).2
      have h0 := (heast j).1
      have h0' := (heast j).2
      rw [eN] at hN
      rw [dN] at hN'
      rw [eM] at h1
      rw [dM] at h1'
      have h := oneSilent_terms.eastStep x y (j : ℤ) hN hN' h1 h1' h0 h0'
      rwa [eN]
  have west : ∀ n : ℕ, 1 ≤ n → x (-(n : ℤ)) = -z n := by
    intro n
    match n with
    | 0 => intro hn; omega
    | 1 =>
      intro _
      have h0 := (hwest 0).2
      have h1 := (hwest 1).2
      norm_num at h0 h1
      have rx := extendedContinuant_recurrence x (-2) 1
      norm_num at rx
      rw [extendedContinuant_neg_two x 1, h0, extendedContinuant_neg_one z 1, h1,
        extendedContinuant_zero z 1] at rx
      have hcon : x (-1) = -z 1 := by omega
      simpa using hcon
    | j + 2 =>
      intro _
      have eN : ((j + 2 : ℕ) : ℤ) = (j : ℤ) + 2 := by omega
      have fN : (-((j + 2 : ℕ) : ℤ) - 2) = -(j : ℤ) - 4 := by omega
      have fN' : (-((j + 2 : ℕ) : ℤ) - 3) = -(j : ℤ) - 5 := by omega
      have dN : ((j + 2 : ℕ) : ℤ) - 1 = (j : ℤ) + 1 := by omega
      have eM : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by omega
      have fM : (-((j + 1 : ℕ) : ℤ) - 2) = -(j : ℤ) - 3 := by omega
      have fM' : (-((j + 1 : ℕ) : ℤ) - 3) = -(j : ℤ) - 4 := by omega
      have dM : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
      have hN := (hwest (j + 2)).1
      have hN' := (hwest (j + 2)).2
      have h1 := (hwest (j + 1)).1
      have h1' := (hwest (j + 1)).2
      have h0 := (hwest j).1
      have h0' := (hwest j).2
      rw [fN, eN] at hN
      rw [fN', dN] at hN'
      rw [fM, eM] at h1
      rw [fM', dM] at h1'
      have h := oneSilent_terms.westStep x z (j : ℤ) hN hN' h1 h1' h0 h0'
      have g1 : (-((j + 2 : ℕ) : ℤ)) = -(j : ℤ) - 2 := by omega
      rwa [g1, eN]
  have hz0 : z 0 = 0 := by
    have h := (hwest 0).1
    norm_num at h
    rw [extendedContinuant_neg_two x 0, extendedContinuant_zero z 0] at h
    exact h.symm
  exact ⟨east, west, hz0⟩

end

end MetaMathlibExt
