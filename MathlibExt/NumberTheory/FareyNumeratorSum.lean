/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FareyNumeratorFormula
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Farey fractions with bounded numerator

Summing the formula for a single numerator counts the Farey fractions whose
numerators lie in `Finset.Icc 1 m`.
-/

namespace MathlibExt.NumberTheory.FareyNumeratorWanted

/-- **Corollary 4**: for `0 < m < n`, the number of
fractions of `F_n` with numerator at most `m` is
`1 + n ∑_{h ≤ m} φ(h)/h - Φ(m)
  - ∑_{h ≤ m} ∑_{d ∣ h} μ(d) {n/d}`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 4. -/
public theorem sum_fareyNumeratorCount (m n : ℕ)
    (hm : 0 < m) (hmn : m < n) :
    (∑ h ∈ Finset.Icc 1 m, (fareyNumeratorCount n h : ℚ)) =
      1 + (n : ℚ) * ∑ h ∈ Finset.Icc 1 m, (Nat.totient h : ℚ) / h -
        ∑ h ∈ Finset.Icc 1 m, (Nat.totient h : ℚ) -
        ∑ h ∈ Finset.Icc 1 m, ∑ d ∈ h.divisors,
          (ArithmeticFunction.moebius d : ℚ) * (((n % d : ℕ) : ℚ) / d) := by
  have hone : (∑ h ∈ Finset.Icc 1 m, (if h = 1 then 1 else 0 : ℚ)) = 1 := by
    rw [Finset.sum_eq_single 1]
    · simp
    · intro h _ hh
      simp [hh]
    · intro h
      exact (h (Finset.mem_Icc.mpr ⟨le_rfl, hm⟩)).elim
  calc
    (∑ h ∈ Finset.Icc 1 m, (fareyNumeratorCount n h : ℚ)) =
        ∑ h ∈ Finset.Icc 1 m,
          ((if h = 1 then 1 else 0 : ℚ) + (n : ℚ) * ((Nat.totient h : ℚ) / h) -
            (Nat.totient h : ℚ) - ∑ d ∈ h.divisors,
              (ArithmeticFunction.moebius d : ℚ) * (((n % d : ℕ) : ℚ) / d)) := by
      apply Finset.sum_congr rfl
      intro h hh
      obtain ⟨hh₁, hhm⟩ := Finset.mem_Icc.mp hh
      rw [fareyNumeratorCount_formula h n hh₁ (hhm.trans_lt hmn),
        mul_comm (Nat.totient h : ℚ) (n : ℚ), mul_div_assoc]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, hone]

end MathlibExt.NumberTheory.FareyNumeratorWanted
