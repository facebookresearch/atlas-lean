/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RankTwoSpectralFamilies
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Tactic.Ring

/-!
# Characteristic signs and the singular cusp tautological action

The companion matrix checks y squared minus s1 y plus s2. The cusp
normalization x=t squared, y=t cubed has A-basis (1,t). Multiplication by
y is the matrix (0,x squared;x,0), including the singular integral model.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.RankTwoSpectralNormalization

open Matrix Polynomial

variable {R : Type} [CommRing R] [Nontrivial R]

def companion (s1 s2 : R) : Matrix (Fin 2) (Fin 2) R := !![0, -s2; 1, s1]

theorem companion_characteristic (s1 s2 : R) :
    (companion s1 s2).charpoly = X ^ 2 - C s1 * X + C s2 := by
  rw [Matrix.charpoly_fin_two]
  simp [companion, Matrix.trace, Matrix.det_fin_two]

def cuspMatrix (x : R) : Matrix (Fin 2) (Fin 2) R := !![0, x ^ 2; x, 0]

theorem cusp_characteristic (x : R) :
    (cuspMatrix x).charpoly = X ^ 2 - C (x ^ 3) := by
  have htr : (cuspMatrix x).trace = 0 := by simp [cuspMatrix, Matrix.trace]
  have hdet : (cuspMatrix x).det = -(x ^ 3) := by
    simp [cuspMatrix, Matrix.det_fin_two]
    ring
  rw [Matrix.charpoly_fin_two]
  simp [htr, hdet]
  ring

def cuspSection (a b : Polynomial R) : Polynomial R :=
  a.comp (X ^ 2) + X * b.comp (X ^ 2)

omit [Nontrivial R] in
theorem cusp_tautological_action (a b : Polynomial R) :
    X ^ 3 * cuspSection a b = cuspSection (X ^ 2 * b) (X * a) := by
  simp only [cuspSection, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp]
  ring

omit [Nontrivial R] in
theorem cusp_equation_in_normalization : (X ^ 3 : Polynomial R) ^ 2 = (X ^ 2) ^ 3 := by
  ring

end MathlibExtTest.AlgebraicGeometry.RankTwoSpectralNormalization
