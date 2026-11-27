/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.Embedding.StupidTruncInclusion
public import MathlibExt.Algebra.Homology.InitialSegmentShape

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

namespace ComplexShape

example : ¬ (downNatInitialSegment 0).Rel (0 : Fin 1) (0 : Fin 1) := by
  simp

example (n : ℕ) :
    (∃ i, (embeddingDownNatInitialSegment 0).f i = n) ↔ n = 0 := by
  rw [mem_range_embeddingDownNatInitialSegment_iff]
  exact Nat.le_zero

example : (embeddingDownNatInitialSegment 0).IsTruncGE := by
  infer_instance

end ComplexShape

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable (K L : HomologicalComplex C (ComplexShape.down ℕ))

example :
    (K.ιStupidTrunc (ComplexShape.embeddingDownNatInitialSegment 0)).f 0 =
      (K.stupidTruncXIso
        (ComplexShape.embeddingDownNatInitialSegment 0)
        (show (ComplexShape.embeddingDownNatInitialSegment 0).f
          (0 : Fin 1) = 0 from rfl)).hom := by
  exact stupidTruncι.f_eq (i := (0 : Fin 1)) K
    (ComplexShape.embeddingDownNatInitialSegment 0) rfl

example :
    (K.ιStupidTrunc (ComplexShape.embeddingDownNatInitialSegment 0)).f 1 = 0 := by
  apply ιStupidTrunc_f_eq_zero
  intro i hi
  have hzero : i = 0 := Fin.eq_zero i
  subst i
  exact Nat.zero_ne_one hi

example (n : ℕ) :
    Mono ((K.ιStupidTrunc
      (ComplexShape.embeddingDownNatInitialSegment 0)).f n) := by
  infer_instance

example : Mono (K.ιStupidTrunc
    (ComplexShape.embeddingDownNatInitialSegment 0)) := by
  infer_instance

variable {K L}

example (φ : K ⟶ L) :
    stupidTruncMap φ (ComplexShape.embeddingDownNatInitialSegment 0) ≫
        L.ιStupidTrunc (ComplexShape.embeddingDownNatInitialSegment 0) =
      K.ιStupidTrunc (ComplexShape.embeddingDownNatInitialSegment 0) ≫ φ := by
  exact ιStupidTrunc_naturality φ
    (ComplexShape.embeddingDownNatInitialSegment 0)

example :
    (ComplexShape.embeddingDownNatInitialSegment 0).stupidTruncFunctor C ⟶
      𝟭 (HomologicalComplex C (ComplexShape.down ℕ)) :=
  ComplexShape.Embedding.ιStupidTruncNatTrans
    (ComplexShape.embeddingDownNatInitialSegment 0) C

end HomologicalComplex

end
