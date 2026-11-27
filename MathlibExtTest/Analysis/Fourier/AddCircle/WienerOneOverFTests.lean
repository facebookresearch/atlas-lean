/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.AddCircle.WienerOneOverF

/-!
# Tests for Wiener's `1/f` theorem

* The zero function, the constant function `1`, and every Fourier monomial
  lie in the Wiener algebra.
* The sum of two monomials lies in the Wiener algebra.
* Wiener's `1/f` theorem applied to the constant function `1` and to the
  first Fourier monomial produces a reciprocal in the Wiener algebra; the
  reciprocal of the first monomial has modulus `1` everywhere.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.Fourier.WienerOneOverFTests

open MathlibExt.Analysis.WienerOneOverFWanted.Analysis.WienerOneOverF

variable {T : ℝ} [Fact (0 < T)]

/-- The constant function `1` lies in the Wiener algebra. -/
private theorem wiener_one_mem : InWienerAlgebra (1 : C(AddCircle T, ℂ)) := by
  have h : fourierCoeff (1 : C(AddCircle T, ℂ)) = Pi.single 0 1 := by
    have h1 : (1 : C(AddCircle T, ℂ)) = fourier 0 := by
      ext x
      simp
    rw [h1]
    exact fourierCoeff_fourier 0
  show Summable (fourierCoeff (1 : C(AddCircle T, ℂ)))
  rw [h]
  apply summable_of_ne_finset_zero (s := {0})
  intro b hb
  by_cases h : b = 0
  · exact absurd (Finset.mem_singleton.mpr h) hb
  · exact Pi.single_eq_of_ne (M := fun _ : ℤ => ℂ) h 1

/-- Every Fourier monomial lies in the Wiener algebra. -/
private theorem wiener_monomial_mem (n : ℤ) :
    InWienerAlgebra (fourier (T := T) n) := by
  show Summable (fourierCoeff (fourier (T := T) n))
  rw [fourierCoeff_fourier]
  apply summable_of_ne_finset_zero (s := {n})
  intro b hb
  by_cases h : b = n
  · exact absurd (Finset.mem_singleton.mpr h) hb
  · exact Pi.single_eq_of_ne (M := fun _ : ℤ => ℂ) h 1

/-- The zero function lies in the Wiener algebra. -/
example : InWienerAlgebra (0 : C(AddCircle T, ℂ)) := by
  have h : fourierCoeff (0 : C(AddCircle T, ℂ)) = 0 := by
    ext n
    simp [fourierCoeff]
  show Summable (fourierCoeff (0 : C(AddCircle T, ℂ)))
  rw [h]
  exact summable_zero

/-- The constant function `1` lies in the Wiener algebra. -/
example : InWienerAlgebra (1 : C(AddCircle T, ℂ)) := wiener_one_mem

/-- Every Fourier monomial lies in the Wiener algebra. -/
example (n : ℤ) : InWienerAlgebra (fourier (T := T) n) := wiener_monomial_mem n

/-- The sum of two monomials lies in the Wiener algebra. -/
example : InWienerAlgebra (fourier (T := T) 1 + fourier (T := T) (-1)) := by
  have hintf : MeasureTheory.Integrable (⇑(fourier (T := T) 1))
      AddCircle.haarAddCircle :=
    (fourier (T := T) 1).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hintg : MeasureTheory.Integrable (⇑(fourier (T := T) (-1)))
      AddCircle.haarAddCircle :=
    (fourier (T := T) (-1)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  show Summable (fourierCoeff (fourier (T := T) 1 + fourier (T := T) (-1)))
  rw [ContinuousMap.coe_add, fourierCoeff.add hintf hintg]
  exact (wiener_monomial_mem 1).add (wiener_monomial_mem (-1))

/-- Wiener's `1/f` theorem applied to the constant function `1`. -/
example : ∃ g : C(AddCircle T, ℂ),
    (∀ x, g x = ((1 : C(AddCircle T, ℂ)) x)⁻¹) ∧ InWienerAlgebra g := by
  apply wiener_inverse_closed 1 wiener_one_mem
  intro x
  simp

/-- Wiener's `1/f` theorem applied to the first Fourier monomial: the
reciprocal has modulus `1` everywhere and lies in the Wiener algebra. -/
example : ∃ g : C(AddCircle T, ℂ),
    (∀ x, ‖g x‖ = 1) ∧ InWienerAlgebra g := by
  obtain ⟨g, hg, hgW⟩ := wiener_inverse_closed (fourier (T := T) 1)
    (wiener_monomial_mem 1)
    (by
      intro x
      rw [fourier_apply]
      exact Circle.coe_ne_zero _)
  refine ⟨g, fun x => ?_, hgW⟩
  rw [hg x, norm_inv]
  have hnorm : ‖fourier (T := T) 1 x‖ = 1 := by
    rw [fourier_apply]
    exact Circle.norm_coe _
  rw [hnorm, inv_one]

end MathlibExtTest.Analysis.Fourier.WienerOneOverFTests
