/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# The real Hilbert symbol

This file defines the Hilbert symbol on nonzero real numbers through solvability of the
associated binary quadratic equation, and characterizes it by signs.
-/

set_option autoImplicit false

@[expose] public section

/-- **Real Hilbert symbol.** For nonzero real numbers $a$ and $b$, the real Hilbert symbol of $a$
and $b$ is the integer $1$ if there are real numbers $x, y$ with $a x^2 + b y^2 = 1$, and the
integer $-1$ otherwise. -/
noncomputable def realHilbertSymbol (a b : ℝˣ) : ℤ :=
  hilbertSymbol ℝ a b

namespace realHilbertSymbol

/-- **Real Hilbert symbol equal to $1$.** For nonzero real numbers $a$ and $b$, the real Hilbert
symbol of $a$ and $b$ equals $1$ if and only if there are real numbers $x, y$ with
$a x^2 + b y^2 = 1$. -/
@[simp]
theorem eq_one_iff {a b : ℝˣ} :
    realHilbertSymbol a b = 1 ↔
      ∃ x y : ℝ, (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 1 :=
  hilbertSymbol.eq_one_iff

/-- **Real Hilbert symbol equal to $-1$.** For nonzero real numbers $a$ and $b$, the real Hilbert
symbol of $a$ and $b$ equals $-1$ if and only if there are no real numbers $x, y$ with
$a x^2 + b y^2 = 1$. -/
theorem eq_neg_one_iff {a b : ℝˣ} :
    realHilbertSymbol a b = -1 ↔
      ¬∃ x y : ℝ, (a : ℝ) * x ^ 2 + (b : ℝ) * y ^ 2 = 1 :=
  hilbertSymbol.eq_neg_one_iff

/-- **Sign rule for the real Hilbert symbol.** For nonzero real numbers $a$ and $b$, the real
Hilbert symbol of $a$ and $b$ equals $-1$ if and only if $a < 0$ and $b < 0$. -/
theorem eq_neg_one_iff_both_neg {a b : ℝˣ} :
    realHilbertSymbol a b = -1 ↔ (a : ℝ) < 0 ∧ (b : ℝ) < 0 := by
  have key : ∀ {c d : ℝˣ}, 0 < (c : ℝ) →
      ∃ x y : ℝ, (c : ℝ) * x ^ 2 + (d : ℝ) * y ^ 2 = 1 := by
    intro c d hc
    have hcne : (c : ℝ) ≠ 0 := Units.ne_zero c
    have hsq : (Real.sqrt (c : ℝ)) ^ 2 = (c : ℝ) := Real.sq_sqrt hc.le
    have hinv : ((Real.sqrt (c : ℝ))⁻¹) ^ 2 = (c : ℝ)⁻¹ := by
      rw [inv_pow, hsq]
    refine ⟨(Real.sqrt (c : ℝ))⁻¹, 0, ?_⟩
    rw [hinv, mul_inv_cancel₀ hcne]
    simp
  rw [eq_neg_one_iff]
  constructor
  · intro hnot
    by_cases ha : (a : ℝ) < 0
    · by_cases hb : (b : ℝ) < 0
      · exact ⟨ha, hb⟩
      · have hbpos : 0 < (b : ℝ) :=
          lt_of_le_of_ne (not_lt.mp hb) (Ne.symm (Units.ne_zero b))
        obtain ⟨x, y, hxy⟩ := key (c := b) (d := a) hbpos
        exact absurd ⟨y, x, by linear_combination hxy⟩ hnot
    · have hapos : 0 < (a : ℝ) :=
        lt_of_le_of_ne (not_lt.mp ha) (Ne.symm (Units.ne_zero a))
      obtain ⟨x, y, hxy⟩ := key (c := a) (d := b) hapos
      exact absurd ⟨x, y, hxy⟩ hnot
  · rintro ⟨ha, hb⟩ hsol
    obtain ⟨x, y, hxy⟩ := hsol
    have hx : (a : ℝ) * x ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg x)
    have hy : (b : ℝ) * y ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hb.le (sq_nonneg y)
    linarith

/-- **The real Hilbert symbol is $\pm 1$.** For nonzero real numbers $a$ and $b$, the real Hilbert
symbol of $a$ and $b$ equals $1$ or $-1$. -/
theorem eq_one_or_neg_one (a b : ℝˣ) :
    realHilbertSymbol a b = 1 ∨ realHilbertSymbol a b = -1 :=
  hilbertSymbol.eq_one_or_neg_one a b

@[simp]
theorem sq (a b : ℝˣ) : realHilbertSymbol a b ^ 2 = 1 := by
  rcases eq_one_or_neg_one a b with h | h <;> simp [h]

theorem ne_zero (a b : ℝˣ) : realHilbertSymbol a b ≠ 0 := by
  rcases eq_one_or_neg_one a b with h | h <;> simp [h]

end realHilbertSymbol

