/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.IntegralRootDlogModels
import MathlibExt.AlgebraicGeometry.PDivisibleTangentTests
import Mathlib.Algebra.Field.ZMod

/-! A nonzero mu_2 coordinate on a square-zero coefficient ring has
a nonzero integral dlog cotangent class. Reduction to its field point
erases this information, which the geometric bridge must preserve.
-/

open MathlibExt.AlgebraicGeometry.IntegralRootDlogModels
open MathlibExt.AlgebraicGeometry.GroupZeroCotangentModels
open MathlibExt.AlgebraicGeometry.PDivisibleTangentTests

noncomputable section

private abbrev R := ZMod 2

private abbrev test : Test 2 R where
  algebra := CommAlgCat.of R R
  module := ModuleCat.of R R
  nilpotent := ⟨1, by change (2 : R) ^ 1 = 0; decide⟩

private abbrev D := Extension 2 R test

private instance : DecidableEq D := inferInstanceAs (DecidableEq (R × R))
private instance : Fintype D := inferInstanceAs (Fintype (R × R))

private def epsilon : D := TrivSqZeroExt.inr (1 : R)

private def augmentation : AugmentedAlgebra R where
  ring := CommAlgCat.of R D
  augmentation := TrivSqZeroExt.fstHom R test.algebra test.module

private def infinitesimalUnit : augmentation.ringˣ where
  val := (1 + epsilon : D)
  inv := (1 + epsilon : D)
  val_inv := by
    change ((1 + epsilon) * (1 + epsilon) : D) = 1
    decide
  inv_val := by
    change ((1 + epsilon) * (1 + epsilon) : D) = 1
    decide

private def infinitesimalRoot : basedRoots 2 R augmentation 1 :=
  ⟨infinitesimalUnit, by
    constructor
    · apply Units.ext
      change (1 + epsilon) ^ 2 = (1 : D)
      decide
    · rfl⟩

private theorem augmentation_square : (augmentation.ideal R) ^ 2 = ⊥ := by
  apply le_antisymm ?_ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro x hx y hy
  change (x * y : D) = 0
  change (x : D).fst = 0 at hx
  change (y : D).fst = 0 at hy
  have hd : ∀ x y : D, x.fst = 0 → y.fst = 0 → x * y = 0 := by decide
  exact hd x y hx hy

example : basedDlog 2 R augmentation 1 (Additive.ofMul infinitesimalRoot) ≠ 0 := by
  intro h
  have hz := ((augmentation.ideal R).toCotangent_eq_zero
    (basedOrigin 2 R augmentation 1 infinitesimalRoot)).mp h
  rw [augmentation_square] at hz
  have hv := Ideal.mem_bot.mp hz
  change (1 + epsilon - 1 : D) = 0 at hv
  have he : epsilon = 0 := by simpa using hv
  exact (by decide : epsilon ≠ 0) he

example : augmentation.augmentation (1 + epsilon : D) = 1 := rfl
