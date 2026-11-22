/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Analysis.Fourier.CircleProduct
import Mathlib.MeasureTheory.Function.LocallyIntegrable

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

-- Complex coefficients distinguish the shift and conjugation conventions.
example {T : ℝ} [Fact (0 < T)] :
    let F : C(AddCircle T, ℂ) := fourier 0 + Complex.I • fourier 1
    fourierCoeff (fun t => conj (F t) * F t) 1 = Complex.I := by
  intro F
  have hc (m : ℤ) : fourierCoeff F m =
      (if m = 0 then 1 else 0) + Complex.I * (if m = 1 then 1 else 0) := by
    change fourierCoeff ((fourier 0 : AddCircle T → ℂ) +
      Complex.I • (fourier 1 : AddCircle T → ℂ)) m = _
    rw [fourierCoeff.add
      ((fourier 0 : C(AddCircle T, ℂ)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (((fourier 1 : C(AddCircle T, ℂ)).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).smul Complex.I)]
    simp [fourierCoeff.const_smul, fourierCoeff_fourier, Pi.single_apply,
      smul_eq_mul]
  have hs : HasSum (fun m : ℤ => conj (fourierCoeff F m) * fourierCoeff F (m + 1))
      Complex.I := by
    convert hasSum_ite_eq (0 : ℤ) Complex.I using 1
    ext m
    rw [hc, hc]
    by_cases h0 : m = 0
    · subst m; norm_num
    · by_cases h1 : m = 1
      · subst m; norm_num
      · simp [h0, h1]
  exact (circle_correlation_hasSum F 1).unique hs

#print axioms AddCircle.fourierCoeff_modulate
#print axioms AddCircle.circle_correlation_hasSum
