/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RootWeightEvaluationsGroupifiedLineWeightFunctorLaws

/-!
# Tests for groupified root-weight line functor laws

The functor laws imply preservation of three-arrow composites and inverse arrows.

Source: Niels Borne and Angelo Vistoli, *Parabolic sheaves on logarithmic schemes*,
https://arxiv.org/abs/1001.0466v2, Proposition 5.2/Corollary 5.4 and
Theorem 6.1.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsCategories
open MathlibExt.AlgebraicGeometry.ParabolicSheafCategories
open MathlibExt.AlgebraicGeometry.RootWeightEvaluations

namespace MathlibExtTest.AlgebraicGeometry.RootWeightEvaluationsGroupifiedLineWeightFunctorLaws

universe u

example (Y : Scheme.{u}) (P : CommMonCat.{u}) (D : DeligneFaltingsChart Y P)
    (G : GroupifiedChart D) {v w z t : Weight P} (a : v ⟶ w) (b : w ⟶ z) (c : z ⟶ t) :
    lineArrow G (a ≫ b ≫ c) = lineArrow G a ≫ lineArrow G b ≫ lineArrow G c := by
  let K := groupifiedLineWeightFunctorLaws Y P D G
  rw [K.composition, K.composition]

example (Y : Scheme.{u}) (P : CommMonCat.{u}) (D : DeligneFaltingsChart Y P)
    (G : GroupifiedChart D) {v w : Weight P} (a : v ⟶ w) (b : w ⟶ v)
    (hab : a ≫ b = 𝟙 v) (hba : b ≫ a = 𝟙 w) : IsIso (lineArrow G a) := by
  let K := groupifiedLineWeightFunctorLaws Y P D G
  refine ⟨⟨lineArrow G b, ?_, ?_⟩⟩
  · rw [← K.composition, hab, K.identity]
  · rw [← K.composition, hba, K.identity]

end MathlibExtTest.AlgebraicGeometry.RootWeightEvaluationsGroupifiedLineWeightFunctorLaws
