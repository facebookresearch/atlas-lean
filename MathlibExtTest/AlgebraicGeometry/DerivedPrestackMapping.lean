/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation

/-! # Nonlinear natural mapping-space consumer

Squaring in every simplicial algebra is natural as a map of underlying
simplicial sets. Its native mapping zero simplex differs from identity:
on the constant integer algebra it sends 3 to 9.
-/

@[expose] noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.DerivedPrestackMapping

open CategoryTheory Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping

universe u

def squareNatural (k : Type u) [CommRing k] : underlying k ⟶ underlying k where
  app A :=
    { app n := ↾fun x : A.obj n => x * x
      naturality n m f := by
        ext x
        exact ((A.map f).hom.map_mul x x).symm }
  naturality A B f := by
    ext n x
    exact ((f.app n).hom.map_mul x x).symm

def liftedUnderlying (k : Type u) [CommRing k] : Prestack k :=
  underlying k ⋙ liftSimplicial

def squareLifted (k : Type u) [CommRing k] : liftedUnderlying k ⟶ liftedUnderlying k :=
  Functor.whiskerRight (squareNatural k) liftSimplicial

def integerAlgebra : SAlg ℤ :=
  (SimplicialObject.const (CommAlgCat.{0} ℤ)).obj (CommAlgCat.of ℤ ℤ)

theorem square_three :
    ((squareNatural ℤ).app integerAlgebra).app (op (SimplexCategory.mk 0)) (3 : ℤ) = (9 : ℤ) := by
  change (3 : ℤ) * 3 = 9
  norm_num

theorem square_zero_simplex_ne_identity :
    mappingZero ℤ (liftedUnderlying ℤ) (liftedUnderlying ℤ) (squareLifted ℤ) ≠
      mappingZero ℤ (liftedUnderlying ℤ) (liftedUnderlying ℤ) (𝟙 (liftedUnderlying ℤ)) := by
  intro h
  have hn := (mappingZero ℤ (liftedUnderlying ℤ) (liftedUnderlying ℤ)).injective h
  have he := congrArg
    (fun f => ((f.app integerAlgebra).app (op (SimplexCategory.mk 0))
      (ULift.up (3 : ℤ))).down) hn
  change (3 : ℤ) * 3 = 3 at he
  norm_num at he

end MathlibExtTest.AlgebraicGeometry.DerivedPrestackMapping
