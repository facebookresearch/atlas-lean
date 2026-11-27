/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.ReducedFormBounds
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the bounds on reduced binary quadratic forms

The reduced form $x^2 + xy + 6y^2$ has $d = 4 \cdot 6 - 1 = 23$, and $-23$ is a fundamental
discriminant. The tests derive $1 \le \sqrt{23/3}$, $\sqrt{23}/2 < 6 \le 23/3$, and
$q(m, n) \ge 6$ for $n \ne 0$, together with the vanishing of $N_q(t)$ for $t < 6$.
-/

namespace BinaryQuadraticForm.ReducedFormBoundsTest

theorem reduced_one_one_six : IsGaussReduced 1 1 6 :=
  IsGaussReduced.mk (by norm_num) (by norm_num [discrim]) (by norm_num) (by norm_num)
    (fun _ => by norm_num)

theorem fundamental_neg_twenty_three : MetaMathlibExt.IsFundamentalDiscriminant (-23) :=
  Or.inl ⟨(Int.prime_iff_natAbs_prime.mpr (by norm_num)).squarefree, by decide⟩

-- $a \le \sqrt{d/3}$ and $\sqrt d / 2 \le c \le d/(3a)$ at $d = 23$.
example : (1 : ℝ) ≤ √((23 : ℝ) / 3) ∧ √(23 : ℝ) / 2 ≤ 6 ∧ (6 : ℝ) ≤ 23 / 3 := by
  obtain ⟨_, h1, h2, h3⟩ := reduced_one_one_six.coefficient_bounds
  have e : ((4 * 1 * 6 - 1 ^ 2 : ℤ) : ℝ) = 23 := by norm_num
  rw [e] at h1 h2 h3
  refine ⟨by exact_mod_cast h1, by exact_mod_cast h2, ?_⟩
  simpa using h3

-- The strict bound $c > \sqrt d / 2$, from the fundamental discriminant $-23$.
example : √(23 : ℝ) / 2 < 6 := by
  have h := reduced_one_one_six.sqrt_discr_div_two_lt_of_isFundamentalDiscriminant
    (by norm_num; exact fundamental_neg_twenty_three) (by norm_num)
  have e : ((4 * 1 * 6 - 1 ^ 2 : ℤ) : ℝ) = 23 := by norm_num
  rw [e] at h
  exact_mod_cast h

-- $m^2 + mn + 6n^2 \ge 6$ whenever $n \ne 0$.
example (m n : ℤ) (hn : n ≠ 0) : 6 ≤ m ^ 2 + m * n + 6 * n ^ 2 := by
  simpa using reduced_one_one_six.le_eval_of_ne_zero (m := m) hn

-- $N_q(t) = 0$ for $t = 5$.
example :
    {p : ℤ × ℤ | 1 ≤ p.2 ∧ ((1 * p.1 ^ 2 + 1 * p.1 * p.2 + 6 * p.2 ^ 2 : ℤ) : ℝ) ≤ 5}.ncard
      = 0 :=
  reduced_one_one_six.values_off_axis.2.1 5 (by norm_num)

end BinaryQuadraticForm.ReducedFormBoundsTest
