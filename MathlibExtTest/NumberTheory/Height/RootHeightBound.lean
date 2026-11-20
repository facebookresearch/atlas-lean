/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Height.RootHeightBound

@[expose] public section

open AlgebraicCurve Polynomial

/-- exactSource consumer: the original binders apply verbatim. -/
example {p : Polynomial (AlgebraicClosure ℚ)} (hmonic : p.Monic)
    {z : AlgebraicClosure ℚ} (hroot : p.eval z = 0) :
    absLogHeight ![z, 1]
      ≤ absLogHeight (fun k : Fin (p.natDegree + 1) => p.coeff k)
        + Real.log (Real.sqrt (p.natDegree + 1)) :=
  AlgebraicCurve.absLogHeight_root_le_coeff hmonic hroot

/-- The bound applied to the root `0` of the monic polynomial `X`. -/
example :
    absLogHeight ![(0 : AlgebraicClosure ℚ), 1]
      ≤ absLogHeight (fun k : Fin ((X : Polynomial (AlgebraicClosure ℚ)).natDegree + 1) =>
          (X : Polynomial (AlgebraicClosure ℚ)).coeff k)
        + Real.log (Real.sqrt ((X : Polynomial (AlgebraicClosure ℚ)).natDegree + 1)) :=
  AlgebraicCurve.absLogHeight_root_le_coeff (monic_X) (by simp)

/-- Boundary: monicity cannot be dropped. The zero polynomial has every
algebraic number as a root, and it is not monic, so the coefficient side
of the bound (which for the zero polynomial records only zero
coefficients) is not asserted to control arbitrary roots. -/
example : ¬ (0 : Polynomial (AlgebraicClosure ℚ)).Monic := by
  simp [Polynomial.Monic]
