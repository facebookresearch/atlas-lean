/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Cyclotomic.CyclotomicUnitEigenspace

@[expose] public section

open scoped NumberField nonZeroDivisors

/-- Source-faithful consumer for the class-group Galois action on an
ideal class, with the original binders. -/
theorem exactSource_clGalAction_clProj_mk0 (p : ℕ) [NeZero p]
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (d : (ZMod p)ˣ)
    (P : (Ideal (𝓞 K))⁰) :
    JacobiSumStickelberger.clGalAction p K d
        (JacobiSumStickelberger.clProj p (𝓞 K)
          (Additive.ofMul (ClassGroup.mk0 P))) =
      JacobiSumStickelberger.clProj p (𝓞 K) (Additive.ofMul
        (ClassGroup.mk0 (Ideal.mapNonZero
          (JacobiSumStickelberger.clRingAction p K d) P))) :=
  JacobiSumStickelberger.clGalAction_clProj_mk0 p K d P

/-- The omega eigenspace contains zero, and a non-eigenvector boundary:
for `p = 2` the exponent set is empty, so the Stickelberger sum is `0`. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

example : (0 : JacobiSumStickelberger.ModP 5
    (Additive (𝓞 (CyclotomicField 5 ℚ))ˣ)) ∈
    ExtCitation.Cyclotomic.unitsOmegaEigenspace 5 2 :=
  Submodule.zero_mem _

example : Stickelberger.exponentSet 5 = {1, 2} := by decide

example : Stickelberger.eigenvalueScalar 5 = 3 := by decide

example : Stickelberger.exponentSet 2 = ∅ := by decide
