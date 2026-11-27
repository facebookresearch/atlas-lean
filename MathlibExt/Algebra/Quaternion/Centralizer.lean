/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul.lean`
and
`P2M/Sol/S_QuaternionAlgebra_commute_iff_exists_eq_smul_one_add_smul.lean`
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

public import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

@[expose] public section

open scoped Quaternion

namespace QuaternionAlgebra

/-- An element of a rational quaternion algebra commutes with a given
element `α` whose imaginary part is not all zero if and only if it lies
in the rational span of `1` and `α`.

Thus the centralizer of a non-scalar quaternion is the two-dimensional
space spanned by `1` and the quaternion itself. -/
public theorem commute_iff_exists_eq_smul_one_add_smul
    {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (α : ℍ[ℚ,a,b])
    (hnc : ¬ (α.imI = 0 ∧ α.imJ = 0 ∧ α.imK = 0)) (x : ℍ[ℚ,a,b]) :
    x * α = α * x ↔ ∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α := by
  constructor
  · intro h
    obtain ⟨r, i, j, k⟩ := α
    obtain ⟨w, p, q, s⟩ := x
    have hI := congrArg QuaternionAlgebra.imI h
    have hJ := congrArg QuaternionAlgebra.imJ h
    have hK := congrArg QuaternionAlgebra.imK h
    simp only [QuaternionAlgebra.mk_mul_mk] at hI hJ hK
    have eK : p * j = q * i := by
      linear_combination (1 / 2 : ℚ) * hK
    have eJ : p * k = s * i := by
      have h2 : a * (p * k - s * i) = 0 := by
        linear_combination (1 / 2 : ℚ) * hJ
      have h3 := (mul_eq_zero.mp h2).resolve_left ha
      linear_combination h3
    have eI : s * j = q * k := by
      have h2 : b * (s * j - q * k) = 0 := by
        linear_combination (1 / 2 : ℚ) * hI
      have h3 := (mul_eq_zero.mp h2).resolve_left hb
      linear_combination h3
    simp only [not_and_or] at hnc
    rcases hnc with hi | hj | hk
    · refine ⟨w - p / i * r, p / i, ?_⟩
      ext <;> simp
      · field_simp
      · rw [div_mul_eq_mul_div, eq_div_iff hi]
        linear_combination -eK
      · rw [div_mul_eq_mul_div, eq_div_iff hi]
        linear_combination -eJ
    · refine ⟨w - q / j * r, q / j, ?_⟩
      ext <;> simp
      · rw [div_mul_eq_mul_div, eq_div_iff hj]
        linear_combination eK
      · field_simp
      · rw [div_mul_eq_mul_div, eq_div_iff hj]
        linear_combination eI
    · refine ⟨w - s / k * r, s / k, ?_⟩
      ext <;> simp
      · rw [div_mul_eq_mul_div, eq_div_iff hk]
        linear_combination eJ
      · rw [div_mul_eq_mul_div, eq_div_iff hk]
        linear_combination -eI
      · field_simp
  · rintro ⟨c, e, rfl⟩
    simp [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]

end QuaternionAlgebra
