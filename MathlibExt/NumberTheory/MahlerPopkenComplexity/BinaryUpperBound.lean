/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
public import MathlibExt.NumberTheory.MahlerPopkenComplexity

/-!
# Binary upper bound for Mahler–Popken complexity

Campbell's upper bound counts one leaf for each doubling and one more when the appended
binary digit is one.
-/

public section

namespace MathlibExt.NumberTheory.MahlerPopkenComplexityWanted

/-- **Upper bound for the binary Mahler–Popken complexity.** For every natural number $n \ge 2$,
the binary ($2$-ary) Mahler–Popken complexity $\lVert n \rVert_2$ is at most
$\lfloor \log_2 n \rfloor + \nu_2(n) - 1$, where $\nu_2(n)$ is the number of ones in the base-$2$
expansion of $n$.

Source: John M. Campbell, "A Binary Version of the Mahler-Popken
Complexity Function", Theorem 2. -/
theorem mahlerPopkenComplexity_two_le_log_add_digitCount_sub_one
    (n : ℕ) (hn : 2 ≤ n) :
    mahlerPopkenComplexity 2 n ≤
      Nat.log 2 n + (Nat.digits 2 n).count 1 - 1 := by
  have htwo : mahlerPopkenComplexity 2 2 ≤ 1 :=
    mahlerPopkenComplexity_min_le (.leaf 1) rfl
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases hsmall : n < 4
    · obtain rfl | rfl : n = 2 ∨ n = 3 := by omega
      · exact htwo
      · exact mahlerPopkenComplexity_min_le (.add (.leaf 1) (.leaf 0)) rfl
    have hhalf : 2 ≤ n / 2 := by omega
    have hbound := ih (n / 2) (by omega) hhalf
    have hlog := Nat.log_pos (by decide : 1 < 2) hhalf
    have hdouble := mahlerPopkenComplexity_mul_le (m := 2) (a := n / 2) (b := 2)
      (by decide) (by omega) (by decide)
    rw [Nat.log_of_one_lt_of_le (by decide) hn, Nat.digits_def' (by decide) (by omega : 0 < n)]
    rcases Nat.mod_two_eq_zero_or_one n with heven | hodd
    · rw [show n / 2 * 2 = n by omega] at hdouble
      rw [heven, List.count_cons_of_ne (by decide : (0 : ℕ) ≠ 1)]
      omega
    · have hone : mahlerPopkenComplexity 2 1 ≤ 1 :=
        mahlerPopkenComplexity_min_le (.leaf 0) rfl
      have hadd := mahlerPopkenComplexity_add_le (m := 2) (a := n / 2 * 2) (b := 1)
        (by decide) (by omega) (by decide)
      rw [show n / 2 * 2 + 1 = n by omega] at hadd
      rw [hodd, List.count_cons_self]
      omega

end MathlibExt.NumberTheory.MahlerPopkenComplexityWanted
