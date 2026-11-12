/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.SLE.BrownianProductProcess
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov








open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatMech.SLE



theorem brownianCoordinateProcess_measure_edist_rpow_four_ge_le
    (s t : Real) (epsilon : ENNReal) (hepsilon : Ne epsilon 0)
    (hepsilonTop : Ne epsilon (⊤ : ENNReal)) :
    brownianProductLaw {omega | epsilon <=
        edist (brownianCoordinateProcess s omega)
          (brownianCoordinateProcess t omega) ^ (4 : Real)} <=
      ((3 : NNReal) * edist s t ^ (2 : Real)) / epsilon := by
  let f : (Real -> Real) -> ENNReal := fun omega =>
    edist (brownianCoordinateProcess s omega)
      (brownianCoordinateProcess t omega) ^ (4 : Real)
  have hf : AEMeasurable f brownianProductLaw :=
    brownianCoordinateProcess_isKolmogorovProcess.measurable_edist.aemeasurable.pow_const 4
  calc
    brownianProductLaw {omega | epsilon <=
        edist (brownianCoordinateProcess s omega)
          (brownianCoordinateProcess t omega) ^ (4 : Real)} <=
        (∫⁻ omega, f omega ∂brownianProductLaw) / epsilon :=
      meas_ge_le_lintegral_div hf hepsilon hepsilonTop
    _ <= ((3 : NNReal) * edist s t ^ (2 : Real)) / epsilon :=
      ENNReal.div_le_div_right
        (brownianCoordinateProcess_isKolmogorovProcess.kolmogorovCondition s t) epsilon



theorem brownianCoordinateProcess_measure_edist_ge_le
    (s t : Real) (delta : ENNReal) (hdelta : Ne delta 0)
    (hdeltaTop : Ne delta (⊤ : ENNReal)) :
    brownianProductLaw {omega | delta <=
        edist (brownianCoordinateProcess s omega)
          (brownianCoordinateProcess t omega)} <=
      ((3 : NNReal) * edist s t ^ (2 : Real)) / delta ^ (4 : Nat) := by
  have hpowZero : Ne (delta ^ (4 : Nat)) 0 := pow_ne_zero _ hdelta
  have hpowTop : Ne (delta ^ (4 : Nat)) (⊤ : ENNReal) := by
    exact ENNReal.pow_ne_top hdeltaTop
  have hsubset : {omega | delta <=
      edist (brownianCoordinateProcess s omega)
        (brownianCoordinateProcess t omega)} <=
      {omega | delta ^ (4 : Nat) <=
        edist (brownianCoordinateProcess s omega)
          (brownianCoordinateProcess t omega) ^ (4 : Real)} := by
    intro omega homega
    change delta <= edist (brownianCoordinateProcess s omega)
      (brownianCoordinateProcess t omega) at homega
    change delta ^ (4 : Nat) <=
      edist (brownianCoordinateProcess s omega)
        (brownianCoordinateProcess t omega) ^ (4 : Real)
    simpa only [← ENNReal.rpow_natCast] using pow_le_pow_left' homega 4
  exact (measure_mono hsubset).trans
    (brownianCoordinateProcess_measure_edist_rpow_four_ge_le
      s t (delta ^ (4 : Nat)) hpowZero hpowTop)

end StatMech.SLE
