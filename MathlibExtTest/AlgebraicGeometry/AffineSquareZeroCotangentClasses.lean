/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AffineSquareZeroCotangentClasses
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Homology.Single

/-!
The coefficient is the actual kernel of Q plus Q to Q. Multiplication
by a lift (2,7) acts on the kernel element (0,3) by6, independently of
the lift's nilpotent part7. The extension-class target is in degree -1.
-/

noncomputable section
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry.AffineSquareZeroCotangentClasses

private abbrev Dual := TrivSqZeroExt ℚ ℚ
private abbrev projection : Dual →ₐ[ℚ] ℚ := TrivSqZeroExt.fstHom ℚ ℚ ℚ

private def kernelCoordinates : RingHom.ker projection.toRingHom ≃+ ℚ where
  toFun x := x.val.snd
  invFun q := ⟨TrivSqZeroExt.inr q, by rfl⟩
  left_inv x := by
    apply Subtype.ext
    have hx := x.property
    change x.val.fst = 0 at hx
    ext <;> simp [hx]
  right_inv q := rfl
  map_add' _ _ := rfl

private theorem squareZero : (RingHom.ker projection.toRingHom) ^ 2 = ⊥ := by
  apply le_antisymm ?_ bot_le
  rw [pow_two, Ideal.mul_le]
  intro x hx y hy
  change x.fst = 0 at hx
  change y.fst = 0 at hy
  change x * y = 0
  ext <;> simp [hx, hy]

private def exampleExtension : Extension ℚ ℚ where
  ring := Dual
  projection := projection
  surjective q := ⟨TrivSqZeroExt.inl q, rfl⟩
  squareZero := squareZero
  coefficient := ModuleCat.of ℚ ℚ
  kernel := kernelCoordinates
  action e x := by
    have hx := x.property
    change x.val.fst = 0 at hx
    change (e * x.val).snd = e.fst * x.val.snd
    simp [TrivSqZeroExt.snd_mul, hx]

example : exampleExtension.kernel ⟨TrivSqZeroExt.inr (3 : ℚ), by rfl⟩ = (3 : ℚ) := rfl

example : (TrivSqZeroExt.inl (2 : ℚ) + TrivSqZeroExt.inr (7 : ℚ)) *
    TrivSqZeroExt.inr (3 : ℚ) = TrivSqZeroExt.inr (6 : ℚ) := by
  ext <;> norm_num

example : IsZero ((coefficientComplex exampleExtension).X (0 : ℤ)) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (-1)
    exampleExtension.coefficient 0 (by decide)
