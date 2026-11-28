/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Algebra.Quaternion.Recognition

open scoped Quaternion

namespace QuaternionRecognitionTest

/-- Consumer with the original binders and hypotheses. -/
theorem exactSource
    (D : Type*) [Ring D] [Algebra ℚ D] (hdim : Module.finrank ℚ D = 4)
    (hdiv : ∀ x : D, x ≠ 0 → IsUnit x)
    (hcen : ∀ z : D, (∀ x : D, z * x = x * z) → z ∈ Set.range (algebraMap ℚ D)) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (D ≃ₐ[ℚ] ℍ[ℚ, a, b]) :=
  exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four D hdim hdiv hcen

/-- A higher-universe consumer: the same statement over `Type 1`. -/
theorem exactSourceType1
    (D : Type 1) [Ring D] [Algebra ℚ D] (hdim : Module.finrank ℚ D = 4)
    (hdiv : ∀ x : D, x ≠ 0 → IsUnit x)
    (hcen : ∀ z : D, (∀ x : D, z * x = x * z) → z ∈ Set.range (algebraMap ℚ D)) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (D ≃ₐ[ℚ] ℍ[ℚ, a, b]) :=
  exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four D hdim hdiv hcen

/-- Consumer of the form stated with `DivisionRing` and `Algebra.IsCentral`. -/
theorem exactSourceCentral
    (D : Type*) [DivisionRing D] [Algebra ℚ D] [Algebra.IsCentral ℚ D]
    (hdim : Module.finrank ℚ D = 4) :
    ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (D ≃ₐ[ℚ] ℍ[ℚ, a, b]) :=
  Algebra.IsCentral.exists_nonempty_algEquiv_quaternionAlgebra_of_finrank_eq_four D hdim

/-- The dimension hypothesis matters: `ℚ` itself is a division algebra
with centre `ℚ`, but it is not a quaternion algebra. -/
example : ¬ ∃ a b : ℚ, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (ℚ ≃ₐ[ℚ] ℍ[ℚ, a, b]) := by
  rintro ⟨a, b, ha, hb, ⟨e⟩⟩
  have h := LinearEquiv.finrank_eq e.toLinearEquiv
  simp [QuaternionAlgebra.finrank_eq_four] at h

end QuaternionRecognitionTest
