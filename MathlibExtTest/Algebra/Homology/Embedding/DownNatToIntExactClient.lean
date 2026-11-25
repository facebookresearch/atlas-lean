/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.Embedding.DownNatToIntExact

@[expose] public section

open CategoryTheory Category Limits

universe v u

namespace ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Public client pinning the Nat-to-Int connecting-morphism equality. -/
public theorem delta_extendDownNatToInt_client
    (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact)
    (n : ℕ) (hijNat : (ComplexShape.down ℕ).Rel (n + 1) n)
    (hijInt : (ComplexShape.down ℤ).Rel (((n + 1 : ℕ) : ℤ)) ((n : ℤ)))
    [S.X₁.HasHomology (n + 1)] [S.X₂.HasHomology (n + 1)] [S.X₃.HasHomology (n + 1)]
    [S.X₁.HasHomology n] [S.X₂.HasHomology n] [S.X₃.HasHomology n]
    [((S.map (ComplexShape.embeddingDownNatToInt.extendFunctor C)).X₁.HasHomology
      (((n + 1 : ℕ) : ℤ)))]
    [((S.map (ComplexShape.embeddingDownNatToInt.extendFunctor C)).X₂.HasHomology
      (((n + 1 : ℕ) : ℤ)))]
    [((S.map (ComplexShape.embeddingDownNatToInt.extendFunctor C)).X₃.HasHomology
      (((n + 1 : ℕ) : ℤ)))]
    [((S.map (ComplexShape.embeddingDownNatToInt.extendFunctor C)).X₁.HasHomology
      ((n : ℤ)))]
    [((S.map (ComplexShape.embeddingDownNatToInt.extendFunctor C)).X₂.HasHomology
      ((n : ℤ)))]
    [((S.map (ComplexShape.embeddingDownNatToInt.extendFunctor C)).X₃.HasHomology
      ((n : ℤ)))] :
    (S.X₃.extendHomologyIso ComplexShape.embeddingDownNatToInt rfl).hom ≫
      hS.δ (n + 1) n hijNat =
      (map_extendFunctor ComplexShape.embeddingDownNatToInt S hS).δ
        (((n + 1 : ℕ) : ℤ)) ((n : ℤ)) hijInt ≫
        (S.X₁.extendHomologyIso ComplexShape.embeddingDownNatToInt rfl).hom :=
  delta_extendDownNatToInt S hS n hijNat hijInt

end ShortComplex.ShortExact

end
