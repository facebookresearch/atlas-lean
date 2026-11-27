/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.FormClassGroup

/-!
# Tests for the form class group

Knapp's discriminant $-20$ example after Proposition 1.9: the aligned forms $2x^2 + 2xy + 3y^2$
and $3x^2 + 2xy + 2y^2$, with $j = 1$, compose to $6x^2 + 2xy + y^2$, which is properly equivalent
to $x^2 + 5y^2$; so the product of their classes is the identity class. Also: the identity class of
discriminant $-20$ is the class of $(1, 0, 5)$, the class of $(2, 2, 3)$ is its own inverse, and the
positive definite subgroup.
-/

namespace BinaryQuadraticForm.FormClassGroupTest

open FormClass

instance : Fact (¬ IsSquare (-20 : ℤ)) :=
  ⟨by rintro ⟨r, hr⟩; nlinarith [mul_self_nonneg r]⟩

instance : Fact ((-20 : ℤ) % 4 = 0 ∨ (-20 : ℤ) % 4 = 1) := ⟨by decide⟩

noncomputable example : CommGroup (FormClass (-20)) := inferInstance

/-- The class of $2x^2 + 2xy + 3y^2$, of discriminant $-20$. -/
abbrev x₂₂₃ : FormClass (-20) := mk 2 2 3 (by norm_num [discrim]) (by decide)

/-- The class of $3x^2 + 2xy + 2y^2$, of discriminant $-20$. -/
abbrev x₃₂₂ : FormClass (-20) := mk 3 2 2 (by norm_num [discrim]) (by decide)

-- The identity class of discriminant `-20` is the class of `x² + 5y²`.
example : (1 : FormClass (-20)) = mk 1 0 5 (by norm_num [discrim]) (by decide) := by
  rw [one_def, mk_eq_mk_iff]
  norm_num
  exact .refl _

-- Knapp, p. 25: `(2, 2, 3)` and `(3, 2, 2)` are aligned with `j = 1` and compose to `(6, 2, 1)`.
example : x₂₂₃ * x₃₂₂ = mk 6 2 1 (by norm_num [discrim]) (by decide) :=
  mk_mul_mk (j := 1) (by norm_num) (by norm_num)

-- `(6, 2, 1)` is properly equivalent to `(1, 0, 5)`, so the product is the identity class.
example : x₂₂₃ * x₃₂₂ = 1 := by
  rw [mk_mul_mk (j := 1) (by norm_num) (by norm_num) (hd := by norm_num [discrim])
    (hp := by decide), one_def, mk_eq_mk_iff]
  norm_num
  exact (properlyEquivalent_swap 6 2 1).trans
    (by simpa using properlyEquivalent_translate 1 (-2) 6 1)

-- The inverse of the class of `(2, 2, 3)` is the class of `(2, -2, 3)`, which is the same class.
example : x₂₂₃⁻¹ = x₂₂₃ := by
  rw [inv_mk, mk_eq_mk_iff]
  simpa using properlyEquivalent_translate 2 (-2) 3 1

example : x₂₂₃ * x₂₂₃ = 1 := by
  have h : x₂₂₃⁻¹ = x₂₂₃ := by
    rw [inv_mk, mk_eq_mk_iff]
    simpa using properlyEquivalent_translate 2 (-2) 3 1
  nth_rw 2 [← h]
  exact mul_inv_cancel x₂₂₃

-- The product is commutative and associative.
example (x y z : FormClass (-20)) : x * (y * z) = z * (y * x) := by
  rw [mul_comm y x, mul_comm z]
  exact (mul_assoc x y z).symm

-- Both classes are positive definite.
example : x₂₂₃ * x₃₂₂ ∈ posDefSubgroup (-20) (by norm_num) :=
  mul_mem ((mk_mem_posDefSubgroup _).mpr (by norm_num))
    ((mk_mem_posDefSubgroup _).mpr (by norm_num))

-- The class of `-x² - 5y²` (of discriminant `-20`) is not positive definite.
example : mk (-1) 0 (-5) (by norm_num [discrim]) (by decide) ∉
    posDefSubgroup (-20 : ℤ) (by norm_num) := by
  rw [mk_mem_posDefSubgroup]
  norm_num

-- Theorem 1.12(b) at the level of forms: the translates `(2, 14, 27)` of `(2, 2, 3)` and
-- `(3, 14, 18)` of `(3, 2, 2)` are aligned with `j = 9`, so their composition `(6, 14, 9)` is
-- properly equivalent to `(6, 2, 1)`.
example : ProperlyEquivalent (2 * 3, 2, 1) (2 * 3, 14, 9) := by
  have h₁ : ProperlyEquivalent (2, 2, 3) (2, 14, 27) := by
    simpa using properlyEquivalent_translate 2 2 3 3
  have h₂ : ProperlyEquivalent (3, 2, 2) (3, 14, 18) := by
    simpa using properlyEquivalent_translate 3 2 2 2
  exact composition_class_well_defined (by decide) (by decide)
    (by rintro ⟨r, hr⟩; norm_num [discrim] at hr; nlinarith [mul_self_nonneg r])
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) h₁ h₂

end BinaryQuadraticForm.FormClassGroupTest
