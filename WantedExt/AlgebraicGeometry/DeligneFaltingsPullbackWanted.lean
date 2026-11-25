/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImageFunctors
public import MathlibExt.AlgebraicGeometry.ParabolicSheafCategories

/-!
# Native Deligne--Faltings inverse images and line groupification

Construct the actual natural inverse-image functor, characterized on every
etale line/section generator, and the cartesian line extension on the actual
Grothendieck group. These are shared construction dependencies for coherent
denominator roots and the source-normalized parabolic comparison.

Sources: Borne--Vistoli, https://arxiv.org/abs/1001.0466v2,
Proposition3.9/Remark3.11 and §§4--5. Native site/sheaf inverse-image and
ordinary module tensor/pullback operations are completed source mathematics.
The geometric root-stack, universal-root and π_*(F⊗Λ_v) equivalence are
separate continuing interfaces; no such conclusion is assumed here.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
open MathlibExt.AlgebraicGeometry.DeligneFaltingsInverseImageFunctors
open MathlibExt.AlgebraicGeometry.ParabolicSheafCategories

universe u

/-- The functor's native pullback and all generator morphisms are fixed. -/
def_wanted dfInverseImageFunctor (X T : Scheme.{u}) (f : T ⟶ X)
    [HasInverseImage f] (A : MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves.MonoidSheaf X) : InverseImageFunctor f A

/-- Extend the actual DF line functor to actual groupification weights,
with full cartesian/unit/multiplication/section comparisons. -/
def_wanted groupifiedDeligneFaltings (X : Scheme.{u})
    (A : MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves.MonoidSheaf X) (D : Structure A) : GroupifiedDF D
