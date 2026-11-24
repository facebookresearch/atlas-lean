/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.IndianBuffet

@[expose] public section

open Filter Topology Finset MathlibExt.Probability.IndianBuffet
open scoped NNReal

namespace MathlibExtTest.Probability.IndianBuffet

/-- Two objects sharing one feature. -/
def Z₁ : Fin 2 → Fin 1 → Bool := fun _ _ => true

example : featureCount Z₁ 0 = 2 := by decide

example : historyFactorial Z₁ = 1 := by decide

/-- Non-vacuity: `H_2 = 3/2`, so the empty columns contribute `exp(-3α/2)` for `N = 2`. -/
example (α : ℝ) : Tendsto (fun K : ℕ => emptyColumnsFactor α 2 K) atTop
    (𝓝 (Real.exp (-(3 / 2 * α)))) := by
  have h : ((harmonic 2 : ℚ) : ℝ) = 3 / 2 := by norm_num [harmonic]
  have := tendsto_emptyColumnsFactor α 2
  rwa [h, show -α * (3 / 2 : ℝ) = -(3 / 2 * α) by ring] at this

/-- The Indian buffet process formula for one shared feature among two objects:
`α exp(-3α/2) / 2`. -/
example (α : ℝ) : lofProb α Z₁ = α * Real.exp (-α * (3 / 2)) / 2 := by
  have hf : featureCount Z₁ 0 = 2 := by decide
  have hh : historyFactorial Z₁ = 1 := by decide
  simp only [lofProb, hf, hh, Fin.prod_univ_one]
  norm_num [harmonic, Nat.factorial]
  ring_nf

example (α : ℝ) : Tendsto (fun K : ℕ => finiteLofProb α K Z₁) atTop (𝓝 (lofProb α Z₁)) :=
  tendsto_finiteLofProb α Z₁

/-- The closed-form expected number of ones never exceeds `N α`. -/
example (K : ℕ) : expectedOnes 2 5 K ≤ 10 := by
  have := expectedOnes_le (α := 2) (by norm_num) 5 K
  norm_num at this ⊢
  linarith

/-- Equation 16 for `N = 3`: `H_3 = 11/6`. -/
example : ∑ j ∈ range 3, ((Nat.choose 3 (j + 1) : ℝ) * (j.factorial * (3 - (j + 1)).factorial)) /
    (Nat.factorial 3) = 11 / 6 := by
  rw [sum_choose_mul_factorial_div]; norm_num [harmonic]

/-- There are three histories with one one among three objects. -/
example : #{h : Fin 3 → Bool | onesCount h = 1} = 3 := by
  rw [card_filter_onesCount_eq]; rfl

/-- Product of Poisson probabilities for one shared feature among two objects. -/
example (α : ℝ≥0) :
    ∏ h ∈ ({h | 0 < onesCount h} : Finset (Fin 2 → Bool)),
      (ProbabilityTheory.poissonMeasure (historyRate α h)).real {historyCount Z₁ h} =
        lofProb α Z₁ :=
  prod_poissonMeasure_historyCount α Z₁ fun k => by fin_cases k; decide

/-- Random Poisson history counts: the count event of `Z₁` has the Indian buffet process
probability. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} (α : ℝ≥0)
    {K : (Fin 2 → Bool) → Ω → ℕ} (hind : ProbabilityTheory.iIndepFun K P)
    (hmeas : ∀ h, Measurable (K h))
    (hlaw : ∀ h ∈ ({h | 0 < onesCount h} : Finset (Fin 2 → Bool)),
      ProbabilityTheory.HasLaw (K h) (ProbabilityTheory.poissonMeasure (historyRate α h)) P) :
    P.real {ω | ∀ h ∈ ({h | 0 < onesCount h} : Finset (Fin 2 → Bool)),
      K h ω = historyCount Z₁ h} = lofProb α Z₁ :=
  measureReal_historyCount_eq_lofProb α Z₁ (fun k => by fin_cases k; decide) hind hmeas hlaw

end MathlibExtTest.Probability.IndianBuffet
