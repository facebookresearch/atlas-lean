/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.Pell

/-!
# Positive solutions of the Pell equation of norm one in ℤ[√3]

The fundamental solution is `2 + √3`, since 2 is the least integer greater than 1.
-/

public section

namespace MathlibExt.NumberTheory.PowerfulNumbersWanted

/-- **Positive solutions of $x^2 - 3y^2 = 1$.** For integers $x$ and $y$, we have $x > 0$,
$y > 0$ and $x^2 - 3y^2 = 1$ if and only if $x + y\sqrt{3} = (2 + \sqrt{3})^k$ in
$\mathbb{Z}[\sqrt{3}]$ for some natural number $k \ge 1$. Writing
$(2 + \sqrt{3})^k = u_k + v_k \sqrt{3}$ for $k \ge 0$, we have $(u_1, v_1) = (2, 1)$,
$(u_2, v_2) = (7, 4)$, and $u_{k+2} = 4u_{k+1} - u_k$ and $v_{k+2} = 4v_{k+1} - v_k$ for
every $k \ge 0$.

Source: Tsz Ho Chan, "A Note on Three Consecutive Powerful Numbers",
Lemma 5. -/
theorem pell_three_eq_one_positive_solutions_iff_and_recurrence :
    (∀ x y : ℤ,
      (0 < x ∧ 0 < y ∧ x ^ 2 - 3 * y ^ 2 = 1) ↔
        ∃ k : ℕ, 1 ≤ k ∧
          (⟨x, y⟩ : ℤ√3) = (⟨2, 1⟩ : ℤ√3) ^ k) ∧
      (((⟨2, 1⟩ : ℤ√3) ^ 1).re = 2 ∧ ((⟨2, 1⟩ : ℤ√3) ^ 1).im = 1 ∧
        ((⟨2, 1⟩ : ℤ√3) ^ 2).re = 7 ∧ ((⟨2, 1⟩ : ℤ√3) ^ 2).im = 4 ∧
        ∀ k : ℕ,
          ((⟨2, 1⟩ : ℤ√3) ^ (k + 2)).re =
              4 * ((⟨2, 1⟩ : ℤ√3) ^ (k + 1)).re -
                ((⟨2, 1⟩ : ℤ√3) ^ k).re ∧
            ((⟨2, 1⟩ : ℤ√3) ^ (k + 2)).im =
              4 * ((⟨2, 1⟩ : ℤ√3) ^ (k + 1)).im -
                ((⟨2, 1⟩ : ℤ√3) ^ k).im) := by
  let a : Pell.Solution₁ 3 := .mk 2 1 (by decide)
  have ha : Pell.IsFundamental a :=
    ⟨by decide, by decide, fun {_} hb => Int.add_one_le_of_lt hb⟩
  have hpow (k : ℕ) : (↑(a ^ k) : ℤ√3) = (⟨2, 1⟩ : ℤ√3) ^ k :=
    map_pow (unitary (ℤ√3)).subtype a k
  constructor
  · intro x y
    constructor
    · rintro ⟨hx, hy, h⟩
      obtain ⟨k, hk⟩ := ha.eq_pow_of_nonneg (a := .mk x y h) hx hy.le
      refine ⟨k, ?_, (congrArg (fun b : Pell.Solution₁ 3 => (b : ℤ√3)) hk).trans (hpow k)⟩
      apply Nat.pos_of_ne_zero
      rintro rfl
      have : y = 0 := congrArg Pell.Solution₁.y (hk.trans (pow_zero a))
      omega
    · rintro ⟨k, hk, heq⟩
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      rw [← hpow] at heq
      have hx : x = (a ^ (n + 1)).x := congrArg Zsqrtd.re heq
      have hy : y = (a ^ (n + 1)).y := congrArg Zsqrtd.im heq
      rw [hx, hy]
      exact ⟨Pell.Solution₁.x_pow_pos ha.x_pos _,
        Pell.Solution₁.y_pow_succ_pos ha.x_pos ha.2.1 _, (a ^ (n + 1)).prop⟩
  · refine ⟨by decide, by decide, by decide, by decide, fun k => ?_⟩
    rw [pow_succ _ (k + 1), pow_succ _ k]
    constructor <;> simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] <;> ring

end MathlibExt.NumberTheory.PowerfulNumbersWanted
