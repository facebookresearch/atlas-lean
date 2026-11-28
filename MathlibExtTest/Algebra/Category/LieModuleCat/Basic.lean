/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.LieModuleCat.Restriction
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.ZMod.Basic
public meta import Mathlib.Tactic.NormNum

/-!
# Lie-module maps and restriction on matrices over the integers modulo six

The adjoint module of two-by-two matrices has [E₀₁,E₁₀] with diagonal entries 1 and −1.
The examples test categorical addition and scalar multiplication, the forgetful functor,
and restriction along the zero Lie map, which changes this nonzero action to zero.
-/

@[expose] public section

namespace LieModuleCat.ReviewTests

open CategoryTheory

abbrev R := ZMod 6
abbrev Mat := Matrix (Fin 2) (Fin 2) R

instance matLieRing : LieRing Mat := LieRing.ofAssociativeRing
instance matLieAlgebra : LieAlgebra R Mat := LieAlgebra.ofAssociativeAlgebra

abbrev adjoint : LieModuleCat R Mat := LieModuleCat.of R Mat Mat

def x : Mat := !![0, 1; 0, 0]
def y : Mat := !![0, 0; 1, 0]

lemma commutator_00 : (⁅x, y⁆ : Mat) 0 0 = 1 := by
  norm_num [LieRing.of_associative_ring_bracket, Matrix.mul_apply, Fin.sum_univ_two, x, y]

example : Preadditive (LieModuleCat R Mat) := inferInstance
example : Linear R (LieModuleCat R Mat) := inferInstance
example : (LieModuleCat.forget R Mat).Additive := inferInstance
example : (LieModuleCat.restrict (0 : Mat →ₗ⁅R⁆ Mat)).Linear R := inferInstance

example : (⁅x, (y : adjoint)⁆ : adjoint) 0 0 = 1 := commutator_00

example :
    (@Bracket.bracket Mat
      (LieModuleCat.restrictObj (0 : Mat →ₗ⁅R⁆ Mat) adjoint).carrier
      (LieModuleCat.lieRingModule
        (LieModuleCat.restrictObj (0 : Mat →ₗ⁅R⁆ Mat) adjoint)).toBracket x y) 0 0 = 0 ∧
        (⁅x, y⁆ : Mat) 0 0 = 1 := by
  constructor
  · simpa using congrArg (fun m : adjoint => m 0 0)
      (LieModuleCat.restrictObj_lie (0 : Mat →ₗ⁅R⁆ Mat) adjoint x y)
  · exact commutator_00

example : ((LieModuleCat.forget R Mat).map ((2 : R) • 𝟙 adjoint)).hom y 1 0 = 2 := by
  change ((2 : R) • y) 1 0 = 2
  norm_num [y]

end LieModuleCat.ReviewTests
