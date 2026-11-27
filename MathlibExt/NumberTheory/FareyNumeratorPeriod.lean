/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FareyNumeratorFormula
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Periodicity of the Farey numerator count

Increasing the Farey order by a multiple of the numerator leaves the remainder sum in
`fareyNumeratorCount_formula` unchanged.

## References

* Rogelio Tomás García, [Farey Fractions with Equal Numerators and the Rank of Unit
  Fractions](https://math.colgate.edu/~integers/y63/y63.pdf), *INTEGERS* 24 (2024),
  Article A63, pp. 1–9, Corollary 2 (p. 5), using Theorem 1 (pp. 3–4).
-/

namespace MathlibExt.NumberTheory.FareyNumeratorWanted

open Finset ArithmeticFunction

/-- **Corollary 2**: for `0 < h < n` and `m ≥ 0`,
`N_{n + m h}(h) = N_n(h) + m φ(h)`.

Source: Rogelio Tomás García, "Farey Fractions with
Equal Numerators and the Rank of Unit Fractions",
INTEGERS 24 (2024), Article A63, Corollary 2. -/
public theorem fareyNumeratorCount_add_mul (h n m : ℕ)
    (hh : 0 < h) (hhn : h < n) :
    fareyNumeratorCount (n + m * h) h =
      fareyNumeratorCount n h + m * Nat.totient h := by
  have hsum :
      (∑ d ∈ h.divisors, (moebius d : ℚ) * (((n + m * h) % d : ℕ) / (d : ℚ))) =
        ∑ d ∈ h.divisors, (moebius d : ℚ) * ((n % d : ℕ) / (d : ℚ)) := by
    apply sum_congr rfl
    intro d hd
    have hdiv : d ∣ m * h := (Nat.dvd_of_mem_divisors hd).trans (dvd_mul_left h m)
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, Nat.add_zero, Nat.mod_mod]
  have hhq : (h : ℚ) ≠ 0 := by exact_mod_cast hh.ne'
  have hlinear :
      (h.totient : ℚ) * (↑(n + m * h) : ℚ) / h =
        (h.totient : ℚ) * n / h + (m : ℚ) * h.totient := by
    push_cast
    field_simp
  have hq : (fareyNumeratorCount (n + m * h) h : ℚ) =
      (fareyNumeratorCount n h : ℚ) + (m : ℚ) * h.totient := by
    rw [fareyNumeratorCount_formula h (n + m * h) hh (hhn.trans_le (Nat.le_add_right n _)),
      fareyNumeratorCount_formula h n hh hhn, hsum, hlinear]
    ring
  exact_mod_cast hq

end MathlibExt.NumberTheory.FareyNumeratorWanted
