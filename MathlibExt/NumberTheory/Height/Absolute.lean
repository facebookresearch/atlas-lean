/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Height.NumberField

/-!
# Absolute heights of algebraic numbers

This file supplements Mathlib's absolute-height definitions with elementary bounds and a primitive
integral representative of the rational minimal polynomial.
-/

@[expose] public section

namespace NumberField

open IntermediateField Polynomial

variable {K : Type*} [Field K] [Algebra ℚ K]

/-- **Primitive integral minimal polynomial.** Let $K$ be a field that is an algebra over
$\mathbb{Q}$, let $x \in K$, and let $m_x \in \mathbb{Q}[X]$ be the minimal polynomial of $x$
over $\mathbb{Q}$, with $m_x = 0$ when $x$ is not algebraic over $\mathbb{Q}$. Choose a nonzero
integer $b$ such that $b\,m_x$ has integer coefficients. The primitive integral minimal polynomial
$P_x \in \mathbb{Z}[X]$ of $x$ is the primitive part of $b\,m_x$: when $b\,m_x \neq 0$ it is
$b\,m_x$ divided by the nonnegative greatest common divisor of its coefficients, and when
$b\,m_x = 0$ it is $1$.

Thus for algebraic $x$, $P_x$ is a primitive polynomial with integer coefficients that is a
nonzero rational multiple of $m_x$, determined up to sign, and for nonalgebraic $x$, $P_x = 1$.
The sign is immaterial for applications to Mahler measure. -/
noncomputable def primitiveIntMinpoly (x : K) : ℤ[X] :=
  (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)).primPart

theorem primitiveIntMinpoly_ne_zero (x : K) : primitiveIntMinpoly x ≠ 0 :=
  Polynomial.primPart_ne_zero _

theorem primitiveIntMinpoly_isPrimitive (x : K) :
    (primitiveIntMinpoly x).IsPrimitive :=
  Polynomial.isPrimitive_primPart _

theorem primitiveIntMinpoly_natDegree (x : K) :
    (primitiveIntMinpoly x).natDegree = (minpoly ℚ x).natDegree := by
  rw [primitiveIntMinpoly, Polynomial.natDegree_primPart]
  let q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ x)
  have hmap : (q.map (algebraMap ℤ ℚ)).natDegree = q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective q
  obtain ⟨b, hb, hspec⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (minpoly ℚ x)
  have hsmul : (b • minpoly ℚ x).natDegree = (minpoly ℚ x).natDegree :=
    Polynomial.natDegree_smul (minpoly ℚ x) (nonZeroDivisors.ne_zero hb)
  rw [← hmap, hspec]
  exact hsmul

theorem primitiveIntMinpoly_algHom_eq {L : Type*} [Field L] [Algebra ℚ L]
    (f : K →ₐ[ℚ] L) (hf : Function.Injective f) (x : K) :
    primitiveIntMinpoly (f x) = primitiveIntMinpoly x := by
  simp only [primitiveIntMinpoly, minpoly.algHom_eq f hf x]

theorem absMulHeight₁_pos {L : Type*} [Field L] [CharZero L] (x : L) :
    0 < absMulHeight₁ x := by
  rw [absMulHeight₁]
  split_ifs with hx
  · let _ : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
      IntermediateField.adjoin.finiteDimensional hx
    let _ : NumberField (IntermediateField.adjoin ℚ {x}) := {}
    exact Real.rpow_pos_of_pos (Height.mulHeight₁_pos _) _
  · exact zero_lt_one

theorem one_le_absMulHeight₁ {L : Type*} [Field L] [CharZero L] (x : L) :
    1 ≤ absMulHeight₁ x := by
  rw [absMulHeight₁]
  split_ifs with hx
  · let _ : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {x}) :=
      IntermediateField.adjoin.finiteDimensional hx
    let _ : NumberField (IntermediateField.adjoin ℚ {x}) := {}
    exact Real.one_le_rpow (Height.one_le_mulHeight₁ _) (by positivity)
  · rfl

theorem absLogHeight₁_nonneg {L : Type*} [Field L] [CharZero L] (x : L) :
    0 ≤ absLogHeight₁ x := by
  rw [absLogHeight₁]
  exact Real.log_nonneg (one_le_absMulHeight₁ x)

end NumberField
