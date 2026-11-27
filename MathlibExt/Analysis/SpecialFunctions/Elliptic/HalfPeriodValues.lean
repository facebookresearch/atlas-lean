/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# The values of the Weierstrass function at the half-periods

For a period pair `ω₁, ω₂` with lattice `Λ`, the half-periods `ω₁ / 2`, `ω₂ / 2` and
`(ω₁ + ω₂) / 2` are not in `Λ`, the derivative `℘'` vanishes there, and the values
`eₖ = ℘(uₖ)` are roots of `4 X³ - g₂ X - g₃`
(`PeriodPair.half_period_values`).

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>: Chapter III, §3, proof of Lemma 3.6, p. 95.
-/

@[expose] public section

open scoped PeriodPair

namespace PeriodPair

variable (L : PeriodPair)

/-- At a point `u ∉ Λ` with `2u ∈ Λ`, the derivative of `℘` vanishes, since `℘'` is odd and
periodic. -/
private lemma derivWeierstrassP_eq_zero_of_two_mul_mem {u : ℂ} (h : 2 * u ∈ L.lattice) :
    ℘'[L] u = 0 := by
  have h₁ : ℘'[L] u = ℘'[L] (-u) := by
    have := L.derivWeierstrassP_add_coe (-u) ⟨2 * u, h⟩
    rw [show -u + ((⟨2 * u, h⟩ : L.lattice) : ℂ) = u by push_cast; ring] at this
    exact this
  rw [derivWeierstrassP_neg] at h₁
  have h₂ : (2 : ℂ) * ℘'[L] u = 0 := by linear_combination h₁
  simpa using h₂

private lemma half_mem_aux {u : ℂ} (hu : u ∉ L.lattice) (h : 2 * u ∈ L.lattice) :
    u ∉ L.lattice ∧ ℘'[L] u = 0 ∧ 4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0 := by
  have hd := L.derivWeierstrassP_eq_zero_of_two_mul_mem h
  refine ⟨hu, hd, ?_⟩
  have := L.derivWeierstrassP_sq u hu
  rw [hd] at this
  linear_combination -this

/-- **The values of the Weierstrass function at the half-periods.** Let `L` be a period pair:
complex numbers `ω₁, ω₂` that are linearly independent over `ℝ`, with lattice
`Λ = ℤ ω₁ + ℤ ω₂`, let `℘` be its Weierstrass function, `℘'` the derivative of `℘`, and `g₂`,
`g₃` its invariants. Let `u₁ = ω₁ / 2`, `u₂ = ω₂ / 2`, `u₃ = (ω₁ + ω₂) / 2` and `eₖ = ℘(uₖ)` for
`k = 1, 2, 3`. Then for `k = 1, 2, 3`, `uₖ ∉ Λ`, `℘'(uₖ) = 0` and `4 eₖ³ - g₂ eₖ - g₃ = 0`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter III, §3, proof of Lemma 3.6, p. 95. -/
theorem half_period_values :
    ∀ u ∈ ({L.ω₁ / 2, L.ω₂ / 2, (L.ω₁ + L.ω₂) / 2} : Set ℂ),
      u ∉ L.lattice ∧ ℘'[L] u = 0 ∧ 4 * ℘[L] u ^ 3 - L.g₂ * ℘[L] u - L.g₃ = 0 := by
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · refine L.half_mem_aux L.ω₁_div_two_notMem_lattice ?_
    rw [mul_div_cancel₀ _ two_ne_zero]
    exact L.ω₁_mem_lattice
  · refine L.half_mem_aux L.ω₂_div_two_notMem_lattice ?_
    rw [mul_div_cancel₀ _ two_ne_zero]
    exact L.ω₂_mem_lattice
  · refine L.half_mem_aux ?_ ?_
    · have h := (mul_ω₁_add_mul_ω₂_mem_lattice (L := L) (α := 1 / 2) (β := 1 / 2)).not.mpr
        (by norm_num)
      convert h using 2
      push_cast
      ring
    · rw [mul_div_cancel₀ _ two_ne_zero]
      exact add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice

end PeriodPair
