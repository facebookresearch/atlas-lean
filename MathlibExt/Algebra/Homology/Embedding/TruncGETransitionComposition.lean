/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.TruncGETransition

/-!
# Composing transitions between good lower truncations

The composite of the native maps through an intermediate cutoff is the
direct native map. The same equality holds for the induced homology maps.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

namespace CochainComplex

universe u v

variable {A : Type u} [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ)

/-- Two consecutive good truncation transitions agree with the direct transition. -/
@[reassoc]
theorem truncGETransition_comp (lo mid hi : ℤ) (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
    K.truncGETransition lo mid h₁ ≫ K.truncGETransition mid hi h₂ =
      K.truncGETransition lo hi (h₁.trans h₂) := by
  apply K.truncGETransition_unique lo hi (h₁.trans h₂)
  calc
    K.πTruncGE lo ≫ K.truncGETransition lo mid h₁ ≫ K.truncGETransition mid hi h₂ =
        K.πTruncGE mid ≫ K.truncGETransition mid hi h₂ :=
      K.πTruncGE_comp_truncGETransition_assoc lo mid h₁ _
    _ = K.πTruncGE hi := K.πTruncGE_comp_truncGETransition mid hi h₂

/-- The direct good truncation transition induces the composite of the two homology maps. -/
theorem homologyMap_truncGETransition_comp (lo mid hi q : ℤ) (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
    homologyMap (K.truncGETransition lo mid h₁) q ≫ homologyMap (K.truncGETransition mid hi h₂) q =
      homologyMap (K.truncGETransition lo hi (h₁.trans h₂)) q := by
  rw [← HomologicalComplex.homologyMap_comp, K.truncGETransition_comp]

end CochainComplex
