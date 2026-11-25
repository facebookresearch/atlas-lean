/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Positive solutions of the generalized Pell equation of norm −2 in ℤ[√3]

We prove Lemma 6 of Tsz Ho Chan's *A Note on Three Consecutive Powerful Numbers*
by descent on the second coordinate.
-/

public section

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

private def pellTerm (k : ℕ) : ℤ√3 :=
  ⟨1, 1⟩ * (⟨2, 1⟩ : ℤ√3) ^ k

private theorem pellTerm_succ (k : ℕ) : pellTerm (k + 1) = pellTerm k * ⟨2, 1⟩ := by
  simp only [pellTerm, pow_succ, mul_assoc]

-- Multiplication by 2 − √3 sends every solution above the seed to a smaller one.
private theorem exists_pellTerm (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : x ^ 2 - 3 * y ^ 2 = -2) : ∃ k : ℕ, (⟨x, y⟩ : ℤ√3) = pellTerm k := by
  by_cases hy₁ : y = 1
  · subst y
    have hx₁ : x = 1 := by nlinarith
    subst x
    exact ⟨0, by simp [pellTerm]⟩
  have hy₂ : 2 ≤ y := by omega
  have hlo : 3 * y < 2 * x :=
    (sq_lt_sq₀ (by omega) (by omega)).mp (by nlinarith [sq_nonneg (y - 2)])
  have hhi : x < 2 * y :=
    (sq_lt_sq₀ hx.le (by omega)).mp (by nlinarith [sq_nonneg y])
  obtain ⟨k, hk⟩ := exists_pellTerm (2 * x - 3 * y) (2 * y - x)
    (by omega) (by omega) (by linear_combination h)
  refine ⟨k + 1, ?_⟩
  rw [pellTerm_succ, ← hk]
  apply Zsqrtd.ext <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring
termination_by y.toNat
decreasing_by omega

private theorem pellTerm_pos (k : ℕ) : 0 < (pellTerm k).re ∧ 0 < (pellTerm k).im := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pellTerm_succ]
    simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]
    constructor <;> omega

/-- **Positive solutions of $x^2 - 3y^2 = -2$.** For integers $x$ and $y$, we have $x > 0$,
$y > 0$ and $x^2 - 3y^2 = -2$ if and only if $x + y\sqrt{3} = (1 + \sqrt{3})(2 + \sqrt{3})^k$
in $\mathbb{Z}[\sqrt{3}]$ for some integer $k \ge 0$. Writing
$(1 + \sqrt{3})(2 + \sqrt{3})^k = u_k + v_k \sqrt{3}$ for $k \ge 0$, we have
$(u_0, v_0) = (1, 1)$, $(u_1, v_1) = (5, 3)$, and $u_{k+2} = 4u_{k+1} - u_k$ and
$v_{k+2} = 4v_{k+1} - v_k$ for every $k \ge 0$.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 6. -/
theorem pell_three_eq_neg_two_positive_solutions_iff_and_recurrence :
    (∀ x y : ℤ,
      (0 < x ∧ 0 < y ∧ x ^ 2 - 3 * y ^ 2 = -2) ↔
        ∃ k : ℕ,
          (⟨x, y⟩ : ℤ√3) = (⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ k) ∧
      ((((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ 0).re = 1 ∧
          ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ 0).im = 1 ∧
          ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ 1).re = 5 ∧
          ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ 1).im = 3) ∧
        ∀ k : ℕ,
          ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ (k + 2)).re =
              4 * ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ (k + 1)).re -
                ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ k).re ∧
            ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ (k + 2)).im =
              4 * ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ (k + 1)).im -
                ((⟨1, 1⟩ : ℤ√3) * (⟨2, 1⟩ : ℤ√3) ^ k).im) := by
  constructor
  · intro x y
    constructor
    · rintro ⟨hx, hy, h⟩
      exact exists_pellTerm x y hx hy h
    · rintro ⟨k, hk⟩
      change (⟨x, y⟩ : ℤ√3) = pellTerm k at hk
      have hpos := pellTerm_pos k
      rw [← hk] at hpos
      refine ⟨hpos.1, hpos.2, ?_⟩
      have hnorm := congrArg (Zsqrtd.normMonoidHom (d := 3)) hk
      rw [pellTerm, map_mul, map_pow] at hnorm
      change x * x - 3 * y * y = -2 * (1 : ℤ) ^ k at hnorm
      simpa [pow_two, mul_assoc] using hnorm
  · refine ⟨by decide, ?_⟩
    intro k
    change (pellTerm (k + 1 + 1)).re = 4 * (pellTerm (k + 1)).re - (pellTerm k).re ∧
      (pellTerm (k + 1 + 1)).im = 4 * (pellTerm (k + 1)).im - (pellTerm k).im
    rw [pellTerm_succ (k + 1), pellTerm_succ k]
    constructor <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

end MathlibExt.NumberTheory.PowerfulNumbersWanted
