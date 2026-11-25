/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.DownNatToIntShift

/-!
# Inverse naturality for shifted-extension homology

The inverse homology comparison for zero extension above a specified
integer lower bound commutes with the homology maps induced by chain maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Inverse naturality of the shifted-extension component comparison. -/
@[reassoc (attr := simp)]
theorem extendDownNatToIntShiftXIso_inv_naturality
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) (b : ℤ) (n : ℕ) :
    (extendDownNatToIntShiftXIso K b n).inv ≫
        (extendMap φ (ComplexShape.embeddingDownNatToIntShift b)).f (b + n) =
      φ.f n ≫ (extendDownNatToIntShiftXIso L b n).inv := by
  simpa only [extendDownNatToIntShiftXIso] using
    extendXIso_inv_naturality
      (ComplexShape.embeddingDownNatToIntShift b) φ
      (show (ComplexShape.embeddingDownNatToIntShift b).f n = b + n by
        rw [ComplexShape.embeddingDownNatToIntShift_f])

/-- Inverse naturality of the shifted-extension homology comparison. -/
@[reassoc]
theorem homologyIso_extendDownNatToIntShift_inv_naturality
    {K L : ChainComplex C ℕ} (φ : K ⟶ L) (b : ℤ) (n : ℕ) :
    (homologyIsoExtendDownNatToIntShift K b n).inv ≫
        homologyMap
          (extendMap φ (ComplexShape.embeddingDownNatToIntShift b)) (b + n) =
      homologyMap φ n ≫
        (homologyIsoExtendDownNatToIntShift L b n).inv := by
  change
    (K.extendHomologyIso
        (ComplexShape.embeddingDownNatToIntShift b) rfl).inv ≫
        homologyMap
          (extendMap φ (ComplexShape.embeddingDownNatToIntShift b)) (b + n) =
      homologyMap φ n ≫
        (L.extendHomologyIso
          (ComplexShape.embeddingDownNatToIntShift b) rfl).inv
  exact (extendHomologyIso_inv_naturality φ
    (ComplexShape.embeddingDownNatToIntShift b) rfl).symm

end HomologicalComplex
