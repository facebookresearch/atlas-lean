/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The real extension of the harmonic numbers at natural inputs

## References

* Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
  Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, pp. 1–15,
  Section 3.1 (p. 10, definition of `H(x)` and the identity `H(n) = Hₙ`).
  <https://math.colgate.edu/~integers/aa86/aa86.pdf>
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The real extension of the harmonic numbers.** For a real number $x$, let

$$H(x) = \int_0^1 \frac{t^x - 1}{t - 1}\,dt,$$

where $t^x$ is the real power and the integral is the Lebesgue integral over $[0, 1]$, taken to be
$0$ when the integrand is not integrable.

This extends the harmonic numbers: $H(n) = 1 + \frac{1}{2} + \cdots + \frac{1}{n}$ for every
natural number $n$.

Source: Idris Assani, Aiden Chester, and Alex Paschal, *On Robin's Inequality and the
Kaneko-Lagarias Inequality*, INTEGERS 26 (2026), Article A86, Section 3.1 (definition of `H(x)`). -/
noncomputable def harmonicExtension (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (t ^ x - 1) / (t - 1)

end

/-- **The real extension agrees with the harmonic numbers.** Let
$H(x) = \int_0^1 \frac{t^x - 1}{t - 1}\,dt$ for real $x$ be the real extension of the harmonic
numbers. For every natural number $n$, $H(n) = H_n$, where $H_n = \sum_{i=1}^n 1/i$ is the
$n$-th harmonic number.

Source: Assani, Chester, and Paschal, INTEGERS 26 (2026), Article A86, Section 3.1 ("`H(n) = H_n`
for all `n ∈ ℕ`"). -/
public theorem harmonicExtension_natCast (n : ℕ) :
    harmonicExtension n = harmonic n := by
  unfold harmonicExtension
  calc
    (∫ t in (0 : ℝ)..1, (t ^ (n : ℝ) - 1) / (t - 1)) =
        ∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.range n, t ^ k := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro t ht
      have hne : t - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_lt ht.2)
      change (t ^ (n : ℝ) - 1) / (t - 1) = ∑ k ∈ Finset.range n, t ^ k
      rw [Real.rpow_natCast, ← geom_sum_mul, mul_div_cancel_right₀ _ hne]
    _ = ∑ k ∈ Finset.range n, ∫ t in (0 : ℝ)..1, t ^ k :=
      intervalIntegral.integral_finsetSum fun k _ => (continuous_id.pow k).intervalIntegrable 0 1
    _ = harmonic n := by
      simp only [integral_pow, one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, one_div,
        harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_add, Nat.cast_one]
      push_cast
      rfl

end MetaMathlibExt
