/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.RightLieModuleCat.Basic
public import MathlibExtTest.Algebra.Category.LieModuleCat.Basic

/-!
# Negative right actions and the Lie-module equivalence

The adjoint matrix module over ZMod 6 has a nonzero commutator. Left-to-right conversion
negates it, right-to-left conversion restores it, and both equivalence components retain
the nonzero coefficient E₁₀.
-/

@[expose] public section

namespace RightLieModuleCat.ReviewTests

open CategoryTheory LieModuleCat.ReviewTests

noncomputable abbrev right := RightLieModuleCat.fromLeft adjoint

example : (RightLieModuleCat.toLeftFunctor (R := R) (L := Mat)).Full := inferInstance
example : (RightLieModuleCat.toLeftFunctor (R := R) (L := Mat)).Faithful := inferInstance
example : (RightLieModuleCat.fromLeftFunctor (R := R) (L := Mat)).Linear R := inferInstance

example : right.action x y 0 0 = (-1 : R) ∧ right.action x y ≠ 0 := by
  have h : right.action x y 0 0 = (-1 : R) := by
    rw [RightLieModuleCat.fromLeft_action]
    change -((⁅x, y⁆ : Mat) 0 0) = (-1 : R)
    rw [commutator_00]
  refine ⟨h, ?_⟩
  intro hz
  have h' := congrArg (fun a : Mat => a 0 0) hz
  rw [h] at h'
  norm_num at h'

example : (⁅x, (y : RightLieModuleCat.toLeft right)⁆ :
    RightLieModuleCat.toLeft right) 0 0 = 1 := by
  rw [RightLieModuleCat.toLeft_lie, RightLieModuleCat.fromLeft_action]
  simpa only [neg_neg] using commutator_00

example :
    ((RightLieModuleCat.equivalence (R := R) (L := Mat)).unitIso.hom.app right).toLinearMap
      y 1 0 = 1 ∧
    (RightLieModuleCat.equivalence (R := R) (L := Mat)).counitIso.hom.app adjoint y 1 0 = 1 := by
  change (y 1 0 = 1) ∧ (y 1 0 = 1)
  norm_num [y]

end RightLieModuleCat.ReviewTests
