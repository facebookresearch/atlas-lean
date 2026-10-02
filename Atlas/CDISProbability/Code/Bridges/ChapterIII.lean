/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.Probability.Kernel.CondDistrib

/-!
# CDIS Probabilités III: bridge statement (V3 sample)

* id 53 (conditional Fubini theorem). For a pair `(X, Y)` of real random variables there is a
  family of probabilities `P_{Y | X = x}` with
  `P_{X,Y}(B₁ × B₂) = ∫_{B₁} P_{Y | X = x}(B₂) P_X(dx)`, unique `P_X`-almost everywhere, and
  `E[g(X, Y)] = ∫ (∫ g(x, y) P_{Y | X = x}(dy)) P_X(dx)`.

In Mathlib the family is the Markov kernel `condDistrib Y X P`.
-/

open MeasureTheory ProbabilityTheory Set

namespace CDIS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X Y : Ω → ℝ}

/-- CDIS P.III, id 53, existence: `condDistrib Y X P` satisfies the rectangle formula. -/
theorem map_prod_apply_prod_eq_lintegral_condDistrib (hX : Measurable X) (hY : Measurable Y)
    {B₁ B₂ : Set ℝ} (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) :
    P.map (fun ω ↦ (X ω, Y ω)) (B₁ ×ˢ B₂) = ∫⁻ x in B₁, condDistrib Y X P x B₂ ∂(P.map X) := by
  rw [← compProd_map_condDistrib hX.aemeasurable hY.aemeasurable,
    Measure.compProd_apply_prod hB₁ hB₂]

/-- CDIS P.III, id 53, uniqueness: any Markov kernel satisfying the rectangle formula is equal
to `condDistrib Y X P` for `P_X`-almost every `x`. -/
theorem condDistrib_ae_eq_of_rectangles (hX : Measurable X) (hY : Measurable Y)
    (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (hκ : ∀ {B₁ B₂ : Set ℝ}, MeasurableSet B₁ → MeasurableSet B₂ →
      P.map (fun ω ↦ (X ω, Y ω)) (B₁ ×ˢ B₂) = ∫⁻ x in B₁, κ x B₂ ∂(P.map X)) :
    condDistrib Y X P =ᵐ[P.map X] κ := by
  have : IsProbabilityMeasure (P.map fun ω ↦ (X ω, Y ω)) :=
    (Measure.isProbabilityMeasure_map_iff (hX.prodMk hY).aemeasurable).2 ‹_›
  refine condDistrib_ae_eq_of_measure_eq_compProd hX.aemeasurable hY.aemeasurable ?_
  refine Measure.ext_prod fun hB₁ hB₂ ↦ ?_
  rw [hκ hB₁ hB₂, Measure.compProd_apply_prod hB₁ hB₂]

/-- CDIS P.III, id 53, expectation formula: if `g(X, Y)` is integrable,
`E[g(X, Y)] = ∫ (∫ g(x, y) P_{Y | X = x}(dy)) P_X(dx)`. -/
theorem integral_comp_eq_integral_condDistrib (hX : Measurable X) (hY : Measurable Y)
    {g : ℝ × ℝ → ℝ} (hg : Measurable g) (hint : Integrable (fun ω ↦ g (X ω, Y ω)) P) :
    ∫ ω, g (X ω, Y ω) ∂P = ∫ x, ∫ y, g (x, y) ∂(condDistrib Y X P x) ∂(P.map X) := by
  have hXY : AEMeasurable (fun ω ↦ (X ω, Y ω)) P := (hX.prodMk hY).aemeasurable
  have hmap := compProd_map_condDistrib (μ := P) hX.aemeasurable hY.aemeasurable
  rw [← integral_map (f := g) hXY hg.aestronglyMeasurable, ← hmap]
  refine Measure.integral_compProd ?_
  rw [hmap, integrable_map_measure hg.aestronglyMeasurable hXY]
  exact hint

end CDIS
