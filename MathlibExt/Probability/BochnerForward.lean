/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import MathlibExt.Analysis.Fourier.Bochner

/-!
# Bochner forward compatibility

The characteristic-function predicates follow the v1 TheoryOfProbability development.
The positive-definiteness predicate includes reality of the quadratic form, correcting the
v1 definition's missing imaginary-part condition. The complex and real forward implications
use `MathlibExt.Analysis.Fourier.BochnerWanted.bochner`, the existing full Bochner theorem.
-/

@[expose] public section

open MeasureTheory Complex
open scoped ComplexConjugate

namespace ProbabilityTheory

/-- A complex-valued function is positive definite when each finite quadratic form
`∑ i, ∑ j, φ (t i - t j) * z i * conj (z j)` is real and nonnegative. -/
def IsPositiveDefinite (φ : ℝ → ℂ) : Prop :=
  ∀ (n : ℕ) (t : Fin n → ℝ) (z : Fin n → ℂ),
    let S := ∑ i, ∑ j, φ (t i - t j) * z i * starRingEnd ℂ (z j)
    S.im = 0 ∧ 0 ≤ S.re

/-- A real-valued function is positive definite when its complex embedding is. -/
def IsPositiveDefiniteReal (φ : ℝ → ℝ) : Prop :=
  IsPositiveDefinite ((↑) ∘ φ)

/-- A function is characteristic when it is the characteristic function of a probability
measure on `ℝ`. -/
def IsCharacteristicFun (φ : ℝ → ℂ) : Prop :=
  ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ ∀ t, charFun μ t = φ t

/-- A real-valued function is characteristic when its complex embedding is. -/
def IsCharacteristicFunReal (φ : ℝ → ℝ) : Prop :=
  IsCharacteristicFun ((↑) ∘ φ)

/-- Every characteristic function of a probability measure on `ℝ` is continuous,
positive definite, and takes the value `1` at `0`. This compatibility statement follows
from the existing full Bochner theorem. -/
theorem bochner_forward (φ : ℝ → ℂ) (hφ : IsCharacteristicFun φ) :
    Continuous φ ∧ IsPositiveDefinite φ ∧ φ 0 = 1 := by
  obtain ⟨μ, hμ, hμφ⟩ := hφ
  obtain ⟨hcont, h0, hpd⟩ :=
    (MathlibExt.Analysis.Fourier.BochnerWanted.bochner (f := φ)).mpr
      ⟨μ, hμ, fun t => (hμφ t).symm⟩
  refine ⟨hcont, ?_, h0⟩
  intro n t z
  simpa only [starRingEnd_apply, star_star, mul_assoc, mul_comm, mul_left_comm]
    using hpd n t (fun i => star (z i))

/-- Characteristic functions of probability measures have real, nonnegative finite
quadratic forms. -/
theorem charFun_isPositiveDefinite (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsPositiveDefinite (charFun μ) :=
  (bochner_forward (charFun μ) ⟨μ, inferInstance, fun _ => rfl⟩).2.1

/-- Every real-valued characteristic function is continuous, positive definite,
and takes the value `1` at `0`. -/
theorem bochner_forward_real (φ : ℝ → ℝ) (hφ : IsCharacteristicFunReal φ) :
    Continuous φ ∧ IsPositiveDefiniteReal φ ∧ φ 0 = 1 := by
  have hφ' : IsCharacteristicFun ((↑) ∘ φ) := hφ
  obtain ⟨hcont, hpd, h0⟩ := bochner_forward ((↑) ∘ φ) hφ'
  refine ⟨?_, hpd, ?_⟩
  · have hEq : φ = fun x => (Complex.ofReal (φ x)).re := by
      funext x
      simp
    rw [hEq]
    exact Complex.continuous_re.comp hcont
  · have h1 : Complex.ofReal (φ 0) = Complex.ofReal 1 := by
      simpa using h0
    exact Complex.ofReal_injective h1

end ProbabilityTheory
