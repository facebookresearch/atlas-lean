/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney

@[expose] public section

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace AlgebraicTopology.AlexanderWhitney

variable {C : Type u} [Category.{v} C]

theorem frontInclusion_assoc (p q r n : ℕ) (h : p + q + r = n) :
    frontInclusion p q (p + q) rfl ≫ frontInclusion (p + q) r n (by omega) =
      frontInclusion p (q + r) n (by omega) := by
  ext i
  simp [frontInclusion, SimplexCategory.subinterval]

theorem middleInclusion_assoc (p q r n : ℕ) (h : p + q + r = n) :
    backInclusion p q (p + q) rfl ≫ frontInclusion (p + q) r n (by omega) =
      frontInclusion q r (q + r) rfl ≫ backInclusion p (q + r) n (by omega) := by
  ext i
  change i.val + p = i.val + p
  rfl

theorem backInclusion_assoc (p q r n : ℕ) (h : p + q + r = n) :
    backInclusion q r (q + r) rfl ≫ backInclusion p (q + r) n (by omega) =
      backInclusion (p + q) r n (by omega) := by
  ext i
  change (i.val + q) + p = i.val + (p + q)
  omega

@[simp]
theorem frontInclusion_zero_right (n : ℕ) :
    frontInclusion n 0 n (by omega) = 𝟙 ⦋n⦌ := by
  ext i
  simp [frontInclusion, SimplexCategory.subinterval]

@[reassoc]
theorem frontFace_assoc (X : SimplicialObject C) (p q r n : ℕ)
    (h : p + q + r = n) :
    frontFace X (show (p + q) + r = n by omega) ≫
        frontFace X (show p + q = p + q by rfl) =
      frontFace X (show p + (q + r) = n by omega) := by
  have hInc := frontInclusion_assoc p q r n h
  have hOp :
      (frontInclusion (p + q) r n (by omega)).op ≫
          (frontInclusion p q (p + q) rfl).op =
        (frontInclusion p (q + r) n (by omega)).op := by
    simpa only [CategoryTheory.op_comp] using congrArg Quiver.Hom.op hInc
  have hMap := congrArg X.map hOp
  simpa only [frontFace, Functor.map_comp] using hMap

@[reassoc]
theorem middleFace_assoc (X : SimplicialObject C) (p q r n : ℕ)
    (h : p + q + r = n) :
    frontFace X (show (p + q) + r = n by omega) ≫
        backFace X (show p + q = p + q by rfl) =
      backFace X (show p + (q + r) = n by omega) ≫
        frontFace X (show q + r = q + r by rfl) := by
  have hInc := middleInclusion_assoc p q r n h
  have hOp :
      (frontInclusion (p + q) r n (by omega)).op ≫
          (backInclusion p q (p + q) rfl).op =
        (backInclusion p (q + r) n (by omega)).op ≫
          (frontInclusion q r (q + r) rfl).op := by
    simpa only [CategoryTheory.op_comp] using congrArg Quiver.Hom.op hInc
  have hMap := congrArg X.map hOp
  simpa only [frontFace, backFace, backInclusion, SimplicialObject.δ₀Iter, Functor.map_comp]
    using hMap

@[reassoc]
theorem backFace_assoc (X : SimplicialObject C) (p q r n : ℕ)
    (h : p + q + r = n) :
    backFace X (show p + (q + r) = n by omega) ≫
        backFace X (show q + r = q + r by rfl) =
      backFace X (show (p + q) + r = n by omega) := by
  have hInc := backInclusion_assoc p q r n h
  have hOp :
      (backInclusion p (q + r) n (by omega)).op ≫
          (backInclusion q r (q + r) rfl).op =
        (backInclusion (p + q) r n (by omega)).op := by
    simpa only [CategoryTheory.op_comp] using congrArg Quiver.Hom.op hInc
  have hMap := congrArg X.map hOp
  simpa only [backFace, backInclusion, SimplicialObject.δ₀Iter, Functor.map_comp] using hMap

@[simp]
theorem frontFace_zero_right (X : SimplicialObject C) (n : ℕ) :
    frontFace X (show n + 0 = n by omega) = 𝟙 _ := by
  rw [frontFace, frontInclusion_zero_right]
  simp

end AlgebraicTopology.AlexanderWhitney
