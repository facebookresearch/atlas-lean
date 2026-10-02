/-
Copyright (c) 2026 Paul-Antoine Bonin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul-Antoine Bonin
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# CDIS Probabilités II: bridge statement (V3 sample)

* id 42: two real random variables with densities `f_X`, `f_Y` are independent iff the pair
  `(X, Y)` has density `f_X(x) f_Y(y)` on `ℝ²`.

Mathlib's `pdf.indepFun_iff_pdf_prod_eq_pdf_mul_pdf` assumes that the pair already has a density.
The course only assumes that `X` and `Y` do, so the faithful statement goes through
`indepFun_iff_map_prod_eq_prod_map_map` and `prod_withDensity` instead.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CDIS

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- CDIS P.II, id 42 (characterisation of independence by densities). -/
theorem indepFun_iff_map_eq_withDensity_mul {X Y : Ω → ℝ} (hX : Measurable X)
    (hY : Measurable Y) {fX fY : ℝ → ℝ≥0∞} (hfX : Measurable fX) (hfY : Measurable fY)
    (hlawX : P.map X = volume.withDensity fX) (hlawY : P.map Y = volume.withDensity fY) :
    IndepFun X Y P ↔
      P.map (fun ω ↦ (X ω, Y ω)) = volume.withDensity (fun z : ℝ × ℝ ↦ fX z.1 * fY z.2) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hlawX, hlawY,
    prod_withDensity hfX hfY, Measure.volume_eq_prod]

end CDIS
