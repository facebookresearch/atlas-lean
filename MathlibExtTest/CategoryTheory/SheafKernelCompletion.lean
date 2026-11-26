/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.SheafKernelCompletion

/-!
# Tests for kernel-adic completion of ring sheaves

In degree zero the finite quotient is the quotient by the kernel itself: kernel elements vanish
there, and the kernel factor recovers the original map. In degree one only products of two kernel
elements are forced to vanish. The tower transitions are compatible with the quotient units, and
after sheafification the completion unit followed by a projection is the quotient unit, while the
completed map restricts to the original map along the completion unit.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open MathlibExt.CategoryTheory.SheafKernelCompletion

namespace MathlibExtTest.SheafKernelCompletion

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R S : Sheaf J CommRingCat.{1}) (θ : R ⟶ S)

/-- Degree zero: the kernel factor composed with the quotient unit is the original map. -/
example : rawUnit R S θ 0 ≫ rawKernelFactor R S θ = θ.hom := by
  ext U a
  rfl

/-- Degree zero: a kernel element vanishes in the zeroth quotient. -/
example (U : Cᵒᵖ) (a : R.obj.obj U) (ha : a ∈ kernelIdeal R S θ U) :
    (rawUnit R S θ 0).app U a = 0 := by
  change Ideal.Quotient.mk _ a = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one]
  exact ha

/-- Degree one: the product of two kernel elements vanishes in the first quotient. -/
example (U : Cᵒᵖ) (a b : R.obj.obj U) (ha : a ∈ kernelIdeal R S θ U)
    (hb : b ∈ kernelIdeal R S θ U) : (rawUnit R S θ 1).app U (a * b) = 0 := by
  change Ideal.Quotient.mk _ (a * b) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, pow_two]
  exact Ideal.mul_mem_mul ha hb

/-- The tower transitions are compatible with the quotient units. -/
example {n m : ℕ} (h : n ≤ m) : rawUnit R S θ m ≫ rawReduction R S θ h = rawUnit R S θ n := by
  ext U a
  rfl

variable [HasSheafify J CommRingCat.{1}]

/-- The completion unit followed by a projection is the sheafified quotient unit. -/
example (n : ℕ) : completionUnit R S θ ≫ projection R S θ n = quotientUnit R S θ n :=
  completionUnit_projection R S θ n

/-- The completed map restricts to the original map along the completion unit. -/
example : completionUnit R S θ ≫ completedTheta R S θ = θ := by
  have h0 : rawUnit R S θ 0 ≫ rawKernelFactor R S θ = θ.hom := by
    ext U a
    rfl
  unfold completedTheta kernelFactor
  rw [completionUnit_projection_assoc]
  unfold quotientUnit
  rw [Adjunction.homEquiv_counit, Category.assoc, ← Functor.map_comp_assoc, h0]
  have hn := (sheafificationAdjunction J CommRingCat.{1}).counit_naturality θ
  erw [hn]
  simp

end MathlibExtTest.SheafKernelCompletion
