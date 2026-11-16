/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing

/-!
# A nonzero simplicial de Rham differential consumer

On the actual constant simplicial algebra Q[x0,x1], d(x0 dx1) is the
nonzero native dx0 wedge dx1 form. This checks the actual form term,
coefficient, differential and exterior-power normalization together.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.AlgebraicGeometry.SimplicialDeRhamModels

open CategoryTheory Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels

abbrev P := MvPolynomial (Fin 2) ℚ

def basis := KaehlerDifferential.mvPolynomialBasis ℚ (Fin 2)

def twoForm : ⋀[P]^2 (Ω[P⁄ℚ]) :=
  exteriorPower.ιMulti P 2 (fun i => basis i)

def area : Module.Dual P (⋀[P]^2 (Ω[P⁄ℚ])) :=
  exteriorPower.pairingDual P (Ω[P⁄ℚ]) 2
    (exteriorPower.ιMulti P 2 (fun i => basis.coord i))

theorem twoForm_ne_zero : twoForm ≠ 0 := by
  intro h
  have ha : area twoForm = 1 := by
    simp [area, twoForm, Matrix.det_fin_two]
  rw [h, map_zero] at ha
  exact zero_ne_one ha

def polynomialAlgebra : SAlg ℚ :=
  (SimplicialObject.const (CommAlgCat ℚ)).obj (CommAlgCat.of ℚ P)

theorem polynomial_differential :
    termDifferential polynomialAlgebra 1 (op (SimplexCategory.mk 0))
      (formGenerator polynomialAlgebra 1 (op (SimplexCategory.mk 0))
        (fun i => MvPolynomial.X i)) = twoForm := by
  change MathlibExt.DeRhamSource.KaehlerDifferential.deRhamDifferential 1
    ((MvPolynomial.X (0 : Fin 2)) • exteriorPower.ιMulti P 1
      (fun i => KaehlerDifferential.D ℚ P (MvPolynomial.X i.succ))) = twoForm
  simpa [twoForm, basis] using
    (MathlibExt.DeRhamSource.KaehlerDifferential.deRhamDifferential_smul_ιMulti_D
      (A := ℚ) (B := P) 1 (fun i => MvPolynomial.X i))

theorem polynomial_differential_nonzero :
    termDifferential polynomialAlgebra 1 (op (SimplexCategory.mk 0))
      (formGenerator polynomialAlgebra 1 (op (SimplexCategory.mk 0))
        (fun i => MvPolynomial.X i)) ≠ 0 := by
  rw [polynomial_differential]
  exact twoForm_ne_zero

end MathlibExtTest.AlgebraicGeometry.SimplicialDeRhamModels
