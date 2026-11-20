/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Analysis.Fourier.CircleProduct

open AddCircle
open scoped ComplexConjugate

-- The zero-frequency case is Parseval for a continuous function.
example {T : ℝ} [Fact (0 < T)] (F : C(AddCircle T, ℂ)) :
    HasSum (fun m : ℤ => conj (fourierCoeff F m) * fourierCoeff F m)
      (fourierCoeff (fun t => conj (F t) * F t) 0) := by
  simpa using circle_correlation_hasSum F 0

-- Zero modulation does not change the coefficient index.
example {T : ℝ} [Fact (0 < T)] (F : C(AddCircle T, ℂ)) (m : ℤ) :
    fourierCoeff (fourier 0 * F : C(AddCircle T, ℂ)) m = fourierCoeff F m := by
  simpa using fourierCoeff_modulate F 0 m

-- Modulating the fifth character by the negative second moves it to frequency three.
example {T : ℝ} [Fact (0 < T)] :
    fourierCoeff (fourier (-2) * fourier 5 : C(AddCircle T, ℂ)) 3 = 1 := by
  rw [fourierCoeff_modulate]
  norm_num [fourierCoeff_fourier]

#print axioms AddCircle.fourierCoeff_modulate
#print axioms AddCircle.circle_correlation_hasSum
