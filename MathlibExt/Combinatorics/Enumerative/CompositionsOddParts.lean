/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Field
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Compositions with an odd number of parts: roots-of-unity partial fractions

For natural numbers `α < β`, with `ζ = e^{2πi/β}`, and a complex number `u` with
`1 - u ^ β ≠ 0`,
`u ^ α / (1 - u ^ β) = (1 / β) ∑_{k < β} ζ ^ (-k α) / (1 - ζ ^ k u)`
(`MetaMathlibExt.pow_div_one_sub_pow_eq_sum`): the partial fraction decomposition of
`u ^ α / (1 - u ^ β)` over the `β`-th roots of unity.

## Proof outline

Since `ζ` is a primitive `β`-th root of unity, `(ζ ^ k u) ^ β = u ^ β`, so no denominator
`1 - ζ ^ k u` vanishes, and the geometric sum gives
`1 / (1 - ζ ^ k u) = (∑_{j < β} (ζ ^ k u) ^ j) / (1 - u ^ β)`. After exchanging the two sums,
the coefficient of `u ^ j / (1 - u ^ β)` is `∑_{k < β} (ζ ^ (j - α)) ^ k`. It is `β` when
`j = α`, and `0` otherwise: for `j ≠ α` with `j, α < β`, `β` does not divide `j - α`, so
`ζ ^ (j - α)` is a `β`-th root of unity different from `1`.

## Implementation notes

`pow_div_one_sub_pow_eq_sum` keeps the full name, the statement and the docstring it had as a
wanted theorem in `WantedExt.Combinatorics.Enumerative.CompositionsOddPartsWanted`, which
imports this module.

## References

The theorem's docstring cites its source, Joshua P. Bowman's *Compositions with an Odd Number of
Parts, and Other Congruences* (Journal of Integer Sequences, 2024). The proof here is
self-contained.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Roots-of-unity partial fraction identity.** Let $\alpha < \beta$ be natural numbers and
let $\zeta = e^{2 \pi i / \beta}$. For every complex number $u$ with $1 - u^\beta \ne 0$,
$$\frac{u^\alpha}{1 - u^\beta} =
\frac{1}{\beta} \sum_{k=0}^{\beta - 1} \frac{\zeta^{-k \alpha}}{1 - \zeta^k u}.$$

Source: Bowman, *Compositions with an Odd Number of Parts, and Other
Congruences*, Journal of Integer Sequences 27 (2024), Article 24.3.6,
Lemma 7 (`jis-2024-24.3.6-lem-7`). -/
public theorem pow_div_one_sub_pow_eq_sum (α β : ℕ) (hα : α < β)
    (u : ℂ) (hu : 1 - u ^ β ≠ 0) :
    u ^ α / (1 - u ^ β)
      = (1 / (β : ℂ)) * ∑ k ∈ Finset.range β,
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ)))
              ^ (-((k : ℤ) * (α : ℤ)))
            / (1 - (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ)))
              ^ k * u) := by
  set ζ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (β : ℂ))
  have hβ0 : β ≠ 0 := by omega
  have hζ : IsPrimitiveRoot ζ β := Complex.isPrimitiveRoot_exp β hβ0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hβ0
  have hβC : (β : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hβ0
  have hpow (k : ℕ) : (ζ ^ k * u) ^ β = u ^ β := by
    rw [mul_pow, ← pow_mul, mul_comm k β, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  -- No denominator vanishes: `ζ ^ k * u = 1` would give `u ^ β = 1`.
  have hden (k : ℕ) : 1 - ζ ^ k * u ≠ 0 := fun h => by
    apply hu
    rw [← hpow k, show ζ ^ k * u = 1 by linear_combination -h, one_pow, sub_self]
  -- Expand each term with the geometric sum `∑_{j < β} (ζ ^ k * u) ^ j`.
  have hterm (k : ℕ) : ζ ^ (-((k : ℤ) * (α : ℤ))) / (1 - ζ ^ k * u)
      = (∑ j ∈ Finset.range β, u ^ j * (ζ ^ ((j : ℤ) - α)) ^ k) / (1 - u ^ β) := by
    have hmul (j : ℕ) : u ^ j * (ζ ^ ((j : ℤ) - α)) ^ k
        = ζ ^ (-((k : ℤ) * (α : ℤ))) * (ζ ^ k * u) ^ j := by
      rw [mul_pow, ← pow_mul, ← zpow_natCast (ζ ^ ((j : ℤ) - α)), ← zpow_mul,
        ← zpow_natCast ζ (k * j), ← mul_assoc, ← zpow_add₀ hζ0, mul_comm]
      congr 2
      push_cast
      ring
    rw [Finset.sum_congr rfl fun j _ => hmul j, ← Finset.mul_sum,
      div_eq_div_iff (hden k) hu, ← hpow k, ← geom_sum_mul_neg]
    ring
  -- Orthogonality: `∑_{k < β} (ζ ^ (j - α)) ^ k` is `β` if `j = α` and `0` otherwise.
  have horth : ∀ j ∈ Finset.range β,
      ∑ k ∈ Finset.range β, (ζ ^ ((j : ℤ) - α)) ^ k = if j = α then (β : ℂ) else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    split_ifs with hjα
    · subst hjα
      simp
    · have hne : ζ ^ ((j : ℤ) - α) ≠ 1 := by
        rw [Ne, hζ.zpow_eq_one_iff_dvd]
        intro hdvd
        have := Int.eq_zero_of_abs_lt_dvd hdvd (abs_lt.mpr ⟨by omega, by omega⟩)
        omega
      rw [geom_sum_eq hne, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        hζ.pow_eq_one, one_zpow, sub_self, zero_div]
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun j hj => by rw [horth j hj]]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range.mpr hα, ↓reduceIte]
  field_simp

end

end MetaMathlibExt
