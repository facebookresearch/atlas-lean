/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels
import MathlibExt.AlgebraicGeometry.IntegralRootDlogModels

/-! Source-origin checks for the original geometric Tate projections and
the integral mu_(p^n) coordinate. Affineness remains an explicit premise
of the group cotangent identification; no field-fibre Lie substitute is
used for the formal p-divisible realization.
-/

open CategoryTheory CategoryTheory.Limits Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
open MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels
open MathlibExt.AlgebraicGeometry.IntegralRootDlogModels
open MathlibExt.Algebra.Module.Torsion

noncomputable section

variable (p : ℕ) [Fact p.Prime] (S : Scheme.{0}) (G : PDivisibleGroup S p)
  (T : Over S)

example (x : GeometricTate p S G T) (n : ℕ) :
    tateModuleTransition p ((points p S G).obj (op T)) n
      (projection p S G T (n + 1) x) = projection p S G T n x :=
  TateModule.levelProj_succ x n

example (n : ℕ) (x : (finitePoints p S G n).obj (op T)) :
    ((finiteToTorsion p S G T n x : TorsionLevel p S G T n) :
      (points p S G).obj (op T)) = (finiteInclusion p S G n).app (op T) x := rfl

example (R : Type) [CommRing R] (n : ℕ) : rootCoordinate p R n ^ (p ^ n) = 1 :=
  root_coordinate_power p R n

#check @MathlibExt.AlgebraicGeometry.GroupZeroCotangentModels.GroupCotangent
#print axioms MathlibExt.Algebra.Module.Torsion.TateModule.mapLinearMap
#print axioms
  MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels.finite_point_torsion
#print axioms MathlibExt.AlgebraicGeometry.PDivisibleGeometricTateModels.finiteToTorsion
#print axioms MathlibExt.AlgebraicGeometry.GroupZeroCotangentModels.groupAugmentation_scalars
#print axioms MathlibExt.AlgebraicGeometry.IntegralRootDlogModels.basedDlog
#print axioms MathlibExt.AlgebraicGeometry.IntegralRootDlogModels.rootDlog
