/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PrismaticCosimplicialAlgebras
import MathlibExt.AlgebraicGeometry.PrismaticAlgebraBaseChange
import Mathlib.RingTheory.Polynomial.Basic

noncomputable section

open CategoryTheory AlgebraicTopology
open MathlibExt.AlgebraicGeometry.PrismaticCosimplicialAlgebras
open MathlibExt.AlgebraicGeometry.PrismaticAlgebraBaseChange
open scoped Simplicial TensorProduct

namespace MathlibExtTest.PrismaticAlgebraCoordinates

/-- Symbolic Frobenius-coordinate map before (p,I)-completion. -/
def squareCoordinate : Polynomial ℤ →+* Polynomial ℤ :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X ^ 2)

/-- The displayed residue coordinate X=2 is applied after the actual nonidentity scalar map. -/
def specialization : Polynomial ℤ →+* ℤ :=
  (Polynomial.evalRingHom (2 : ℤ)).comp squareCoordinate

example : specialization Polynomial.X = 4 := by
  norm_num [specialization, squareCoordinate]

example : specialization Polynomial.X ≠ Polynomial.eval (2 : ℤ) Polynomial.X := by
  norm_num [specialization, squareCoordinate]

def constantAlgebra (R : Type) [CommRing R] : AlgebraDiagram R :=
  (Functor.const SimplexCategory).obj (CommAlgCat.of R (ULift.{1} R))

example : cupRing (constantAlgebra ℤ) 1 2 (ULift.up 3) (ULift.up 5) = ULift.up 15 := by
  rfl

example : cupTensor (constantAlgebra ℤ) 1 2
    (ULift.up 3 ⊗ₜ[ℤ] ULift.up 5) = ULift.up 15 := by
  exact (cupTensor_tmul (constantAlgebra ℤ) 1 2 (ULift.up 3) (ULift.up 5)).trans rfl

/-- The nonidentity scalar test also checks an actual nonzero structural product. -/
example : specialization (Polynomial.X * Polynomial.X) = 16 := by
  norm_num [specialization, squareCoordinate]

example : specialization (Polynomial.X * Polynomial.X) =
    specialization Polynomial.X * specialization Polynomial.X := map_mul _ _ _

/-- Negative cochain parity is retained by absolute value, rather than truncated toNat. -/
example : (-1 : ℤ) ^ (((-1 : ℤ) * 3).natAbs) = -1 := by norm_num

#print axioms MathlibExt.AlgebraicGeometry.PrismaticCosimplicialAlgebras.cupRing_naturality
#print axioms MathlibExt.AlgebraicGeometry.PrismaticAlgebraBaseChange.AlgebraMap.completed_unit
#print axioms MathlibExt.AlgebraicGeometry.PrismaticAlgebraHypermodels.Hypermodel.completedCup_unit

end MathlibExtTest.PrismaticAlgebraCoordinates
