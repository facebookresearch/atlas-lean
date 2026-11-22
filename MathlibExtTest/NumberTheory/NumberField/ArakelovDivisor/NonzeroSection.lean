/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.ArakelovDivisor.NonzeroSection

/-!
# Tests for Proposition 15.9 (nonzero section of a large Arakelov divisor)

At `K = ℚ` there are no complex places and `discr ℚ = 1`, so `B_ℚ = 1`.
The Arakelov divisor with ideal component `1` and radius `2` at the unique
infinite place has size `2 > 1`, so the theorem produces a nonzero section;
that section satisfies `|x| ≤ 2`.
-/

@[expose] public section

open NumberField NumberField.InfinitePlace
open scoped NumberField nonZeroDivisors

/-- The new theorem is available at the expected name and type. -/
example (K : Type) [Field K] [NumberField K] (D : ArakelovDivisor K) :
    (2 / Real.pi) ^ InfinitePlace.nrComplexPlaces K *
        Real.sqrt |(NumberField.discr K : ℝ)| <
      (ArakelovDivisor.sizeHom K D : ℝ) →
    ∃ x ∈ D.sectionSet, x ≠ 0 :=
  ArakelovDivisor.exists_ne_zero_mem_sectionSet_of_size_gt K D

/-- The Arakelov divisor on `ℚ` with ideal component `1` and radius `2`. -/
noncomputable def testDivisor : ArakelovDivisor ℚ :=
  (1, fun _ => ⟨2, by norm_num⟩)

/-- Its size is `2`: the unique infinite place has multiplicity `1` and the
absolute norm of `1` is `1`. -/
theorem testDivisor_sizeHom : (ArakelovDivisor.sizeHom ℚ testDivisor : ℝ) = 2 := by
  rw [ArakelovDivisor.sizeHom_coe]
  simp [testDivisor, FractionalIdeal.absNorm_one]

/-- Its size exceeds `B_ℚ = 1`. -/
example : (2 / Real.pi) ^ InfinitePlace.nrComplexPlaces ℚ *
      Real.sqrt |(NumberField.discr ℚ : ℝ)| <
    (ArakelovDivisor.sizeHom ℚ testDivisor : ℝ) := by
  rw [testDivisor_sizeHom, nrComplexPlaces_eq_zero_of_finrank_eq_one (by simp),
    NumberField.discr_rat]
  norm_num [Real.sqrt_one]

/-- Proposition 15.9 applied to the test divisor: it has a nonzero section,
and every such section satisfies `|x| ≤ 2`. -/
example : ∃ x ∈ testDivisor.sectionSet, x ≠ 0 ∧ |x| ≤ 2 := by
  have hB : (2 / Real.pi) ^ InfinitePlace.nrComplexPlaces ℚ *
        Real.sqrt |(NumberField.discr ℚ : ℝ)| <
      (ArakelovDivisor.sizeHom ℚ testDivisor : ℝ) := by
    rw [testDivisor_sizeHom, nrComplexPlaces_eq_zero_of_finrank_eq_one (by simp),
      NumberField.discr_rat]
    norm_num [Real.sqrt_one]
  obtain ⟨x, hx, hx_ne⟩ :=
    ArakelovDivisor.exists_ne_zero_mem_sectionSet_of_size_gt ℚ testDivisor hB
  refine ⟨x, hx, hx_ne, ?_⟩
  have h := hx.2 default
  rw [Rat.infinitePlace_apply] at h
  have h2 : ((|x| : ℚ) : ℝ) ≤ 2 := by simpa [testDivisor, Rat.cast_abs] using h
  exact_mod_cast h2
