/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ContinuousFKG
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ContinuousFKG`

* Harris–FKG on `[0, 1]²` (`continuous_fkg`) for the bounded monotone function
  `x ↦ arctan (x 0)` paired with itself.
* Chebyshev's inequality on `ℝ` for the uniform measure on `[0, 1]`; `HasFKG` for it.
-/

@[expose] public section

open MeasureTheory
open StatMech.Probability

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ContinuousFKG

/-- `x ↦ arctan (x 0)`: bounded, measurable and monotone on `Fin n → ℝ` for `n ≥ 1`. -/
noncomputable def f (n : ℕ) : (Fin (n + 1) → ℝ) → ℝ := fun x => Real.arctan (x 0)

theorem f_measurable (n : ℕ) : Measurable (f n) :=
  Real.continuous_arctan.measurable.comp (measurable_pi_apply 0)

theorem f_bound (n : ℕ) (x : Fin (n + 1) → ℝ) : |f n x| ≤ Real.pi / 2 :=
  abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩

theorem f_mono (n : ℕ) : Monotone (f n) := fun _ _ h => Real.arctan_strictMono.monotone (h 0)

example : (∫ x, f 1 x ∂(Measure.pi (fun _ : Fin 2 => volume.restrict (Set.Icc (0 : ℝ) 1))))
      * (∫ x, f 1 x ∂(Measure.pi (fun _ : Fin 2 => volume.restrict (Set.Icc (0 : ℝ) 1))))
    ≤ ∫ x, f 1 x * f 1 x ∂(Measure.pi (fun _ : Fin 2 => volume.restrict (Set.Icc (0 : ℝ) 1))) :=
  continuous_fkg 2 (f_measurable 1) (f_measurable 1) (f_bound 1) (f_bound 1) (f_mono 1) (f_mono 1)

example : HasFKG unitMeasure := hasFKG_real unitMeasure

example : (∫ x, Real.arctan x ∂unitMeasure) * (∫ x, Real.arctan x ∂unitMeasure)
    ≤ ∫ x, Real.arctan x * Real.arctan x ∂unitMeasure :=
  chebyshev_correlation_prob unitMeasure Real.continuous_arctan.measurable
    Real.continuous_arctan.measurable
    (fun x => abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩)
    (fun x => abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩)
    Real.arctan_strictMono.monotone Real.arctan_strictMono.monotone

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ContinuousFKG
