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

public import MathlibExt.Algebra.Homology.Embedding.DownNatToInt
public import MathlibExt.Algebra.Homology.Embedding.ExtendExact

/-!
# Short exact sequences under extension from ℕ to ℤ

Zero extension of chain complexes from natural to integer degrees preserves zero
morphisms and short exact sequences. The connecting morphisms agree through the
canonical extension homology isomorphisms.
-/

@[expose] public section

open CategoryTheory Category Limits

universe v u

-- The wrapper functor is definitionally `ComplexShape.embeddingDownNatToInt.extendFunctor`,
-- but the `PreservesZeroMorphisms` instance does not follow by unfolding, so we
-- transport the instance from the underlying `extendFunctor`.
instance {C : Type u} [Category.{v} C] [HasZeroObject C] [HasZeroMorphisms C] :
    (ComplexShape.embeddingDownNatToIntExtendFunctor (C := C)).PreservesZeroMorphisms := by
  change (ComplexShape.embeddingDownNatToInt.extendFunctor C).PreservesZeroMorphisms
  infer_instance

namespace ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Zero-extension from `ChainComplex C ℕ` to `ChainComplex C ℤ` preserves short exactness.

This is the specialization of `map_extendFunctor` to the embedding
`ComplexShape.embeddingDownNatToInt`.  The wrapper functor
`ComplexShape.embeddingDownNatToIntExtendFunctor` is definitionally the same
as `ComplexShape.embeddingDownNatToInt.extendFunctor`, so the result follows
directly from the generic theorem. -/
theorem map_embeddingDownNatToIntExtend
    (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact) :
    (S.map (ComplexShape.embeddingDownNatToIntExtendFunctor C)).ShortExact := by
  simpa [ComplexShape.embeddingDownNatToIntExtendFunctor] using
    (map_extendFunctor (e := ComplexShape.embeddingDownNatToInt) (S := S) hS)

/-- Nat-to-Int specialization needed by R322.

The extended connecting morphism at `((n + 1 : ℕ) : ℤ)` and `(n : ℤ)` agrees
with the original Nat connecting morphism conjugated by the canonical
`extendHomologyIso`s. Both relation proofs are explicit. -/
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
