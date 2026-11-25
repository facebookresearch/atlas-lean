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

public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
public import MathlibExt.Analysis.CStarAlgebra.Module.Product.Basic

/-!
# Compact block-diagonal operators

A binary block-diagonal adjointable operator is compact when both diagonal
entries are Hilbert-module compact.  The proof factors each diagonal block
through the adjointable coordinate projection and inclusion.
-/

@[expose] public section

noncomputable section

namespace CStarModule.AdjointableOperator

universe uB uE uF uE' uF'

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℂ E']
  [SMul Bᵐᵒᵖ E'] [CStarModule Bᵐᵒᵖ E']
variable {F' : Type uF'} [NormedAddCommGroup F'] [NormedSpace ℂ F']
  [SMul Bᵐᵒᵖ F'] [CStarModule Bᵐᵒᵖ F']

/-- Let B be a possibly nonunital complex C-star algebra and let the factors be normed right
C-star modules over B, with their coefficient-valued inner products. If both factor maps are
compact module operators, their block-diagonal product map is compact. -/
theorem prodMap_mem_compact
    {T : AdjointableOperator B E E'}
    {S : AdjointableOperator B F F'}
    (hT : T ∈ compactSubmodule (B := B) (E := E) (F := E'))
    (hS : S ∈ compactSubmodule (B := B) (E := F) (F := F')) :
    prodMap T S ∈ compactSubmodule
      (B := B) (E := WithCStarModule Bᵐᵒᵖ (E × F))
      (F := WithCStarModule Bᵐᵒᵖ (E' × F')) := by
  have hleft :
      (CStarModule.Product.inl (B := B) (E := E') (F := F')).comp
          (T.comp (CStarModule.Product.fst (B := B) (E := E) (F := F))) ∈
        compactSubmodule
          (B := B) (E := WithCStarModule Bᵐᵒᵖ (E × F))
          (F := WithCStarModule Bᵐᵒᵖ (E' × F')) :=
    comp_mem_compact_right _
      (comp_mem_compact_left hT
        (CStarModule.Product.fst (B := B) (E := E) (F := F)))
  have hright :
      (CStarModule.Product.inr (B := B) (E := E') (F := F')).comp
          (S.comp (CStarModule.Product.snd (B := B) (E := E) (F := F))) ∈
        compactSubmodule
          (B := B) (E := WithCStarModule Bᵐᵒᵖ (E × F))
          (F := WithCStarModule Bᵐᵒᵖ (E' × F')) :=
    comp_mem_compact_right _
      (comp_mem_compact_left hS
        (CStarModule.Product.snd (B := B) (E := E) (F := F)))
  exact Submodule.add_mem _ hleft hright

end CStarModule.AdjointableOperator
