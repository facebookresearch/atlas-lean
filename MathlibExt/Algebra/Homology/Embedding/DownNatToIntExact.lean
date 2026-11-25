/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.DownNatToInt
public import MathlibExt.Algebra.Homology.Embedding.ExtendExact

/-!
# Short exact sequences under natural-to-integer zero extension

Zero extension from natural to integer chain degrees preserves short exact
sequences. The canonical homology comparisons commute with the connecting
morphisms of their long exact sequences.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

-- Zero extension preserves zero morphisms.
--
--
instance {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C] :
    (ComplexShape.embeddingDownNatToIntExtendFunctor (C := C)).PreservesZeroMorphisms := by
  change (ComplexShape.embeddingDownNatToInt.extendFunctor C).PreservesZeroMorphisms
  infer_instance

namespace ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Zero extension from natural to integer chain degrees preserves short exactness. -/
theorem map_embeddingDownNatToIntExtend
    (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact) :
    (S.map (ComplexShape.embeddingDownNatToIntExtendFunctor C)).ShortExact := by
  simpa [ComplexShape.embeddingDownNatToIntExtendFunctor] using
    (map_extendFunctor (e := ComplexShape.embeddingDownNatToInt) (S := S) hS)

/-- The connecting morphism after natural-to-integer zero extension agrees
with the original connecting morphism under the canonical homology isomorphisms. -/
theorem delta_extendDownNatToInt
    (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact)
    (n : ℕ) (hijNat : (ComplexShape.down ℕ).Rel (n + 1) n)
    (hijInt : (ComplexShape.down ℤ).Rel (((n + 1 : ℕ) : ℤ)) ((n : ℤ)))
    [S.X₁.HasHomology (n + 1)] [S.X₂.HasHomology (n + 1)] [S.X₃.HasHomology (n + 1)]
    [S.X₁.HasHomology n] [S.X₂.HasHomology n] [S.X₃.HasHomology n] :
    (S.X₃.extendHomologyIso ComplexShape.embeddingDownNatToInt rfl).hom ≫
      hS.δ (n + 1) n hijNat =
      (map_extendFunctor ComplexShape.embeddingDownNatToInt S hS).δ
        (((n + 1 : ℕ) : ℤ)) ((n : ℤ)) hijInt ≫
        (S.X₁.extendHomologyIso ComplexShape.embeddingDownNatToInt rfl).hom :=
  map_extendFunctor_δ ComplexShape.embeddingDownNatToInt S hS (n + 1) n
    (((n + 1 : ℕ) : ℤ)) ((n : ℤ)) rfl rfl hijNat hijInt

end ShortComplex.ShortExact

end
