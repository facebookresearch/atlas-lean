/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.TruncGETransition

/-!
# Composition of good cochain truncation transitions

For integer cochains in an abelian category, the canonical transitions
τ≥lo K → τ≥mid K → τ≥hi K compose to the direct transition whenever
lo≤mid≤hi. The same compatibility holds on homology in every degree.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex

namespace CochainComplex

universe u v

variable {A : Type u} [Category.{v} A] [Abelian A] (K : CochainComplex A ℤ)

/--
Let K be an integer cochain complex in an abelian category A and let lo≤mid≤hi be integers.
Write τ≥m K for its good truncation below degree m and T_{a,b}:τ≥a K→τ≥b K for the canonical
transition when a≤b. The transitions compose as T_{lo,mid} ≫ T_{mid,hi} = T_{lo,hi}. The maps
use the same original complex K at all three cutoffs.
-/
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

/--
Let K be an integer cochain complex in an abelian category A and let lo≤mid≤hi be integers.
Write τ≥m K for its good truncation below degree m and T_{a,b}:τ≥a K→τ≥b K for the canonical
transition when a≤b. For every integer homology degree q, H^q(T_{lo,mid}) ≫ H^q(T_{mid,hi}) =
H^q(T_{lo,hi}). No restriction q≥hi is imposed.
-/
theorem homologyMap_truncGETransition_comp (lo mid hi q : ℤ) (h₁ : lo ≤ mid) (h₂ : mid ≤ hi) :
    homologyMap (K.truncGETransition lo mid h₁) q ≫ homologyMap (K.truncGETransition mid hi h₂) q =
      homologyMap (K.truncGETransition lo hi (h₁.trans h₂)) q := by
  rw [← HomologicalComplex.homologyMap_comp, K.truncGETransition_comp]

end CochainComplex
