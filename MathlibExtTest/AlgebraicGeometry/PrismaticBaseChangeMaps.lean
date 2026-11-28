/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.PrismaticBaseChangeMaps

/-! The comparison tracks scalars through the specified base prism map.
It retains the actual structural ring elements and changes the action
by the given base map, including when that map is not the identity.
-/

open CategoryTheory Opposite
open MathlibExt.RingTheory.BoundedPrisms
open MathlibExt.AlgebraicGeometry.PadicFormalSchemes
open MathlibExt.AlgebraicGeometry.RelativePrismaticSite
open MathlibExt.AlgebraicGeometry.PrismaticBaseChangeMaps

variable (p : ℕ) [Fact p.Prime] (P Q : Prism.{0} p)
  (X : FormalScheme p P.ring P.ideal) (Y : FormalScheme p Q.ring Q.ideal)
  (f : Map p P Q X Y) (U : Obj p Q Y) (a : P.ring)

example : ((f.coefficientIso p P Q X Y).hom.app (op U))
    (a • (ULift.up (1 : U.prism.ring) : (structurePresheaf p P X).obj
      (op ((f.functor p P Q X Y).obj U)))) =
      ULift.up (U.base.hom (f.base.hom a)) := by
  apply ULift.ext
  change U.base.hom (f.base.hom a) * 1 = _
  exact mul_one _

example : ((f.functor p P Q X Y).obj U).base = f.base ≫ U.base := rfl
