/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_
ternary_eq_zero.lean`
and
`P2M/Sol/S_QuadraticForm_forall_quaternary_normForm_eq_zero_iff_forall_
ternary_eq_zero.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

namespace QuadraticFormNormFormAux

variable {K : Type} [Field K] (a b : K)

private theorem quat_of_tern (_ha : a ≠ 0) (_hb : b ≠ 0)
    (h : ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0)
    (x₀ x₁ x₂ x₃ : K) (hq : x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0) :
    x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by
  have hN : x₀ ^ 2 - a * x₁ ^ 2 = b * (x₂ ^ 2 - a * x₃ ^ 2) := by
    linear_combination hq
  by_cases hD : x₂ ^ 2 - a * x₃ ^ 2 = 0
  · have hN0 : x₀ ^ 2 - a * x₁ ^ 2 = 0 := by rw [hN, hD, mul_zero]
    by_cases hx3 : x₃ = 0
    · have hx2 : x₂ = 0 := by
        subst hx3
        have hx2sq : x₂ ^ 2 = 0 := by simpa using hD
        exact sq_eq_zero_iff.mp hx2sq
      obtain ⟨h0, h1, -⟩ := h x₀ x₁ 0 (by rw [hN0]; ring)
      exact ⟨h0, h1, hx2, hx3⟩
    · exfalso
      obtain ⟨-, h3, -⟩ := h x₂ x₃ 0 (by linear_combination hD)
      exact hx3 h3
  · exfalso
    set D := x₂ ^ 2 - a * x₃ ^ 2 with hDdef
    obtain ⟨-, -, h1⟩ := h ((x₀ * x₂ - a * x₁ * x₃) / D)
      ((x₁ * x₂ - x₀ * x₃) / D) 1 (by
        field_simp
        have key : (x₀ * x₂ - a * x₁ * x₃) ^ 2 - a * (x₁ * x₂ - x₀ * x₃) ^ 2 =
            (x₀ ^ 2 - a * x₁ ^ 2) * (x₂ ^ 2 - a * x₃ ^ 2) := by ring
        rw [hN] at key
        linear_combination key)
    exact one_ne_zero h1

private theorem tern_of_quat
    (h : ∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
      x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0)
    (z x y : K) (ht : z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) : z = 0 ∧ x = 0 ∧ y = 0 := by
  obtain ⟨h0, h1, h2, -⟩ := h z x y 0 (by linear_combination ht)
  exact ⟨h0, h1, h2⟩

end QuadraticFormNormFormAux

namespace QuadraticForm

/-- The quaternary norm form `x₀² - a·x₁² - b·x₂² + a·b·x₃²` of the
quaternion algebra `ℍ[K, a, b]` is anisotropic if and only if the ternary
form `z² - a·x² - b·y²` is.

This is the standard reduction of quaternion-algebra isotropy to a ternary
quadratic form. It is used to test whether a quaternion algebra is a
division algebra, in quadratic-form theory (anisotropy of Pfister forms),
and in local-global arguments for quaternion algebras. -/
theorem forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero (K : Type)
    [Field K] (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    (∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
        x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) ↔
      ∀ z x y : K, z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 → z = 0 ∧ x = 0 ∧ y = 0 :=
  ⟨fun h z x y ht => QuadraticFormNormFormAux.tern_of_quat a b h z x y ht,
   fun h x₀ x₁ x₂ x₃ hq =>
    QuadraticFormNormFormAux.quat_of_tern a b ha hb h x₀ x₁ x₂ x₃ hq⟩

end QuadraticForm
