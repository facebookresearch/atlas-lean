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

public import MathlibExt.Algebra.Homology.PartialTotalBasic

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example : ChainComplex C ℕ :=
  B.partialTotal 0

example : B.partialTotal 0 ⟶ B.total (ComplexShape.down ℕ) :=
  B.partialTotalι 0

example (j : ℕ) :
    (B.firstStupidTrunc 0).ιTotal (ComplexShape.down ℕ) 0 j j
          (Nat.zero_add j) ≫
        (B.partialTotalι 0).f j =
      ((B.stupidTruncXIso
        (ComplexShape.embeddingDownNatInitialSegment 0)
        (show (ComplexShape.embeddingDownNatInitialSegment 0).f
          (0 : Fin 1) = 0 from rfl)).hom.f j) ≫
        B.ιTotal (ComplexShape.down ℕ) 0 j j (Nat.zero_add j) := by
  exact B.ιTotal_partialTotalι 0 (0 : Fin 1) j j (Nat.zero_add j)

example (n : ℕ) : Mono ((B.partialTotalι 0).f n) := by
  infer_instance

example : Mono (B.partialTotalι 0) := by
  infer_instance

end HomologicalComplex₂

end
