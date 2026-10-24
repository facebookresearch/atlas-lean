/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.Measure.UniquenessOnRd

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace MathlibExtTest.MeasureTheory.Measure.UniquenessOnRd

/-- The quadrant-uniqueness theorem restates with the exact public
signature. -/
example (d : ℕ) (μ ν : Measure (Fin d → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a : Fin d → ℝ, μ (Iic a) = ν (Iic a)) :
    μ = ν :=
  Measure.ext_of_Iic_pi d μ ν h

/-- The rectangle-uniqueness theorem restates with the exact public
signature. -/
example (d : ℕ) (μ₁ μ₂ : Measure (Fin d → ℝ))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (a b : Fin d → ℝ), (∀ i, a i ≤ b i) →
      μ₁ (univ.pi fun i => Ioc (a i) (b i)) =
        μ₂ (univ.pi fun i => Ioc (a i) (b i))) :
    μ₁ = μ₂ :=
  Measure.eq_of_forall_Ioc_eq d μ₁ μ₂ h

/-- The rectangle-value uniqueness theorem restates with the exact public
signature. -/
example {d : ℕ} (F : (Fin d → ℝ) → ℝ)
    {μ₁ μ₂ : Measure (Fin d → ℝ)}
    (h₁ : ∀ (a b : Fin d → ℝ), (∀ i, a i ≤ b i) →
      μ₁ (univ.pi fun i => Ioc (a i) (b i)) = ENNReal.ofReal (rectangleValue F a b))
    (h₂ : ∀ (a b : Fin d → ℝ), (∀ i, a i ≤ b i) →
      μ₂ (univ.pi fun i => Ioc (a i) (b i)) = ENNReal.ofReal (rectangleValue F a b)) :
    μ₁ = μ₂ :=
  Measure.eq_of_forall_rectangleValue_eq F h₁ h₂

/-- In dimension `1`, the inclusion-exclusion sum over the two vertices of
`(a, b]` is `F b - F a`. -/
theorem rectangleValue_fin_one (F : (Fin 1 → ℝ) → ℝ) (a b : Fin 1 → ℝ) :
    rectangleValue F a b = F b - F a := by
  have hps : (Finset.univ : Finset (Fin 1)).powerset = {∅, {0}} := by decide
  have h0 : rectangleVertex a b ∅ = b := by
    funext i
    simp [rectangleVertex]
  have h1 : rectangleVertex a b {0} = a := by
    funext i
    fin_cases i
    simp [rectangleVertex]
  rw [rectangleValue, hps]
  simp [Finset.sum_insert, Finset.sum_singleton, h0, h1]
  ring

/-- A constant function has zero rectangle value in dimension `1`, since
`F b - F a = c - c`. -/
example (c : ℝ) (a b : Fin 1 → ℝ) :
    rectangleValue (fun _ => c) a b = 0 := by
  rw [rectangleValue_fin_one]
  simp

/-- The zero measure is the unique measure assigning every rectangle the
mass `ENNReal.ofReal (rectangleValue (fun _ => 0) a b) = 0`, via the
rectangle-value theorem. -/
example {d : ℕ} :
    (0 : Measure (Fin d → ℝ)) = (0 : Measure (Fin d → ℝ)) :=
  Measure.eq_of_forall_rectangleValue_eq (fun _ : (Fin d → ℝ) => (0 : ℝ))
    (fun a b _ => by simp [rectangleValue])
    (fun a b _ => by simp [rectangleValue])

/-- Application of quadrant uniqueness: two finite measures on `ℝ²`
agreeing on all quadrants agree on every upper quadrant `Ioi a`. -/
example (μ ν : Measure (Fin 2 → ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a : Fin 2 → ℝ, μ (Iic a) = ν (Iic a)) (a : Fin 2 → ℝ) :
    μ (Ioi a) = ν (Ioi a) := by
  have hEq := Measure.ext_of_Iic_pi 2 μ ν h
  rw [hEq]

/-- Application of rectangle uniqueness: two finite measures on `ℝ²`
agreeing on all rectangles agree on every quadrant `Iic a`. -/
example (μ₁ μ₂ : Measure (Fin 2 → ℝ))
    [IsFiniteMeasure μ₁] [IsFiniteMeasure μ₂]
    (h : ∀ (a b : Fin 2 → ℝ), (∀ i, a i ≤ b i) →
      μ₁ (univ.pi fun i => Ioc (a i) (b i)) =
        μ₂ (univ.pi fun i => Ioc (a i) (b i))) (a : Fin 2 → ℝ) :
    μ₁ (Iic a) = μ₂ (Iic a) := by
  have hEq := Measure.eq_of_forall_Ioc_eq 2 μ₁ μ₂ h
  rw [hEq]

#print axioms MeasureTheory.Measure.ext_of_Iic_pi
#print axioms MeasureTheory.Measure.eq_of_forall_Ioc_eq
#print axioms MeasureTheory.Measure.eq_of_forall_rectangleValue_eq

end MathlibExtTest.MeasureTheory.Measure.UniquenessOnRd
