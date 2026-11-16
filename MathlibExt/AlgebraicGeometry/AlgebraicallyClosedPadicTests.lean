/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# The original O_C and C tests for p-divisible Hodge--Tate realization

C is an arbitrary algebraically closed complete nonarchimedean normed
extension of Q_p, with the norm fixed on every original coefficient.
O_C is literally the norm-at-most-one subring of that field. Integral
and generic scheme points use these actual rings and their inclusion.
No finite-extension, discrete-valuation or spherical-completeness
hypothesis is imposed.

Source: Scholze--Weinstein, arXiv:1211.6357v2, Section 1/Theorem B
and Section 5.1; the recalled Hodge--Tate sequence is over this C.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.AlgebraicallyClosedPadicTests

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- The full source class of algebraically closed complete p-adic extensions. -/
structure FieldTest where
  field : Type
  [normed : NormedField field]
  [closed : IsAlgClosed field]
  [complete : CompleteSpace field]
  [coefficients : Algebra (Padic p) field]
  norm_coefficients : ∀ a : Padic p, ‖algebraMap (Padic p) field a‖ = ‖a‖
  nonarchimedean : ∀ a b : field, ‖a + b‖ ≤ max ‖a‖ ‖b‖

attribute [instance] FieldTest.normed FieldTest.closed FieldTest.complete FieldTest.coefficients

variable (C : FieldTest p)

/-- The original valuation ring O_C, without a separately supplied integral carrier. -/
def integers : Subring C.field where
  carrier := {a | ‖a‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {a b} ha hb := (C.nonarchimedean a b).trans (max_le ha hb)
  neg_mem' {a} ha := by
    change ‖a‖ ≤ 1 at ha
    change ‖-a‖ ≤ 1
    simpa only [norm_neg] using ha
  mul_mem' {a b} ha hb := by
    change ‖a‖ ≤ 1 at ha
    change ‖b‖ ≤ 1 at hb
    change ‖a * b‖ ≤ 1
    rw [norm_mul]
    calc
      ‖a‖ * ‖b‖ ≤ 1 * 1 := mul_le_mul ha hb (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1

/-- The actual inclusion O_C into C. -/
def integerInclusion : integers p C →+* C.field := (integers p C).subtype

/-- Original Z_p coefficients in O_C, through Q_p and the specified field embedding. -/
def padicIntegerScalars : PadicInt p →+* integers p C :=
  (((algebraMap (Padic p) C.field).comp PadicInt.Coe.ringHom)).codRestrict
    (integers p C) (by
      intro a
      change ‖algebraMap (Padic p) C.field (a : Padic p)‖ ≤ 1
      rw [C.norm_coefficients]
      exact a.property)

/-- The integral identity test is the actual original spectrum. -/
abbrev IntegralScheme := Spec (CommRingCat.of (integers p C))

/-- The generic geometric test uses the actual inclusion O_C to C. -/
def genericTest : Over (IntegralScheme p C) :=
  Over.mk (Spec.map (CommRingCat.ofHom (integerInclusion p C)))

end MathlibExt.AlgebraicGeometry.AlgebraicallyClosedPadicTests
