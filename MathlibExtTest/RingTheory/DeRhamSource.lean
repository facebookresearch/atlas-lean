/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.DeRhamSource.Complex
import Mathlib.RingTheory.Kaehler.Polynomial

/-! # Nonzero ordinary de Rham consumer

The differential of X² in Q[X] has coefficient 2X in the native Kähler
basis. It is nonzero, and its next de Rham differential vanishes.
-/

@[expose] noncomputable section

namespace MathlibExtTest.RingTheory.DeRhamSource

open CategoryTheory

abbrev P := Polynomial ℚ

def degreeZeroForm (b : P) : ⋀[P]^0 (Ω[P⁄ℚ]) :=
  b • exteriorPower.ιMulti P 0 (fun _ => KaehlerDifferential.D ℚ P b)

def differentialCoefficient (b : P) : P :=
  KaehlerDifferential.polynomialEquiv ℚ
    (exteriorPower.oneEquiv P (Ω[P⁄ℚ])
      (MathlibExt.DeRhamSource.KaehlerDifferential.deRhamDifferential
        (A := ℚ) (B := P) 0 (degreeZeroForm b)))

theorem differentialCoefficient_eq (b : P) :
    differentialCoefficient b = Polynomial.derivative b := by
  dsimp [differentialCoefficient, degreeZeroForm]
  rw [MathlibExt.DeRhamSource.KaehlerDifferential.deRhamDifferential_smul_ιMulti_D
    (A := ℚ) (B := P) 0 (fun _ => b), exteriorPower.oneEquiv_ιMulti]
  exact KaehlerDifferential.polynomialEquiv_D ℚ b

theorem quadratic_differential :
    differentialCoefficient (Polynomial.X ^ 2) = 2 * Polynomial.X := by
  rw [differentialCoefficient_eq]
  norm_num [Polynomial.C_ofNat]

theorem quadratic_not_closed :
    MathlibExt.DeRhamSource.KaehlerDifferential.deRhamDifferential (A := ℚ) (B := P) 0
      (degreeZeroForm (Polynomial.X ^ 2)) ≠ 0 := by
  intro h
  have hz : differentialCoefficient (Polynomial.X ^ 2) = 0 := by
    simp [differentialCoefficient, h]
  rw [quadratic_differential] at hz
  exact (mul_ne_zero (by norm_num : (2 : P) ≠ 0) Polynomial.X_ne_zero) hz

example :
    ((MathlibExt.DeRhamSource.KaehlerDifferential.deRhamComplex ℚ P).d 0 1).hom
      (degreeZeroForm (Polynomial.X ^ 2)) ≠ 0 := quadratic_not_closed

theorem quadratic_second_differential :
    ((MathlibExt.DeRhamSource.KaehlerDifferential.deRhamComplex ℚ P).d 1 2).hom
      (((MathlibExt.DeRhamSource.KaehlerDifferential.deRhamComplex ℚ P).d 0 1).hom
        (degreeZeroForm (Polynomial.X ^ 2))) = 0 := by
  simp only [MathlibExt.DeRhamSource.KaehlerDifferential.deRhamComplex_d]
  exact MathlibExt.DeRhamSource.KaehlerDifferential.deRhamDifferential_comp_self 0 _

end MathlibExtTest.RingTheory.DeRhamSource
