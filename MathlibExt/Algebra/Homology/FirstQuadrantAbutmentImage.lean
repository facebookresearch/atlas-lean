/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantStablePage
public import MathlibExt.CategoryTheory.Abelian.DiagramLemmas.ImageQuotient

/-!
# The finite abutment as a nested-image quotient

The fixed lower stage `-1` in the stable-page comparison is replaced by the
literal bottom stage.  The resulting canonical abutment term is then computed
from the exact long-homology sequence as a quotient of the image of stage `p`
by the image of stage `p-1`, both taken in stage `p+q+1` homology.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The middle filtration window lies between bottom and the finite upper
abutment stage. -/
theorem horizontalCanonicalAbutmentIndices_le (p q : ℕ) :
    (⊥ : EInt) ≤ horizontalFirstPageLowerIndex p ∧
      horizontalFirstPageUpperIndex p ≤ horizontalAbutmentUpperIndex p q :=
  ⟨bot_le, (horizontalAbutmentIndices_le p q).2⟩

/-- Canonical finite abutment term whose lower index is the literal bottom
stage. -/
noncomputable abbrev horizontalFirstQuadrantCanonicalAbutmentTerm
    (p q : ℕ) : C :=
  let X := horizontalCompleteFiltrationSpectralObject K
  X.E
    (homOfLE (horizontalCanonicalAbutmentIndices_le p q).1)
    (homOfLE (horizontalFirstPageIndex_le p))
    (homOfLE (horizontalCanonicalAbutmentIndices_le p q).2)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
      (-((p + q : ℕ) : ℤ) + 1)

/-- The cochain complex at the bottom filtration stage is zero. -/
theorem horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot :
    IsZero ((horizontalCompleteFiltrationCochainDiagram K).obj (⊥ : EInt)) := by
  change IsZero ((ComplexShape.embeddingDownNat.extendFunctor C).obj
    (horizontalCompleteFilteredTotalComplex K (⊥ : EInt)))
  rw [horizontalCompleteFilteredTotalComplex_bot]
  exact (ComplexShape.embeddingDownNat.extendFunctor C).map_isZero
    HomologicalComplex.isZero_zero

/-- Relative homology from bottom to the finite stage `-1` is zero. -/
theorem horizontalBottomToNegativeRelativeHomologyIsZero (p q : ℕ) :
    IsZero (((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q : ℕ) : ℤ) + 1)).obj
        (mk₁ (homOfLE (show (⊥ : EInt) ≤ horizontalAbutmentLowerIndex
          from bot_le)))) := by
  apply horizontalCompleteFiltrationSpectralObject_H_isZero_of_obj_isZero K
  · exact horizontalCompleteFiltrationCochainDiagram_obj_isZero_bot K
  · exact horizontalCompleteFiltrationCochainDiagram_obj_isZero_of_neg K
      (-1) (by omega)

/-- Replace the finite zero lower stage of the abutment term by bottom. -/
noncomputable def horizontalFiniteToCanonicalAbutmentIso (p q : ℕ) :
    horizontalFirstQuadrantAbutmentTerm K p q ≅
      horizontalFirstQuadrantCanonicalAbutmentTerm K p q := by
  let X := horizontalCompleteFiltrationSpectralObject K
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let n₂ : ℤ := -((p + q : ℕ) : ℤ) + 1
  exact (X.isoMapFourδ₁Toδ₀'
    (⊥ : EInt)
    horizontalAbutmentLowerIndex
    (horizontalFirstPageLowerIndex p)
    (horizontalFirstPageUpperIndex p)
    (horizontalAbutmentUpperIndex p q)
    bot_le
    (horizontalAbutmentIndices_le p q).1
    (horizontalFirstPageIndex_le p)
    (horizontalAbutmentIndices_le p q).2
    n₀ n₁ n₂
    (horizontalBottomToNegativeRelativeHomologyIsZero K p q)).symm

/-- Every sufficiently late page is canonically isomorphic to the
bottom-indexed finite abutment term. -/
noncomputable def horizontalStablePageCanonicalAbutmentIso
    (r : ℤ) (hr : 1 ≤ r) (p q : ℕ)
    (hlower : (p : ℤ) + 1 ≤ r) (hupper : (q : ℤ) + 2 ≤ r) :
    ((horizontalFirstQuadrantSpectralSequence K).page r).X (p, q) ≅
      horizontalFirstQuadrantCanonicalAbutmentTerm K p q :=
  horizontalStablePageAbutmentIso K r hr p q hlower hupper ≪≫
    horizontalFiniteToCanonicalAbutmentIso K p q

/-- Map from bottom to the filtration stage preceding column `p`. -/
noncomputable abbrev horizontalCanonicalAbutmentLowerMap (p : ℕ) :
    (⊥ : EInt) ⟶ horizontalFirstPageLowerIndex p :=
  homOfLE bot_le

/-- Inclusion of the two consecutive filtration stages around column `p`. -/
noncomputable abbrev horizontalCanonicalAbutmentMiddleMap (p : ℕ) :
    horizontalFirstPageLowerIndex p ⟶ horizontalFirstPageUpperIndex p :=
  homOfLE (horizontalFirstPageIndex_le p)

/-- Inclusion of stage `p` into the finite upper abutment stage. -/
noncomputable abbrev horizontalCanonicalAbutmentUpperMap (p q : ℕ) :
    horizontalFirstPageUpperIndex p ⟶ horizontalAbutmentUpperIndex p q :=
  homOfLE (horizontalAbutmentIndices_le p q).2

/-- Composite map from bottom to stage `p`. -/
noncomputable abbrev horizontalCanonicalAbutmentLowerCompositeMap (p : ℕ) :
    (⊥ : EInt) ⟶ horizontalFirstPageUpperIndex p :=
  homOfLE bot_le

/-- Composite map from bottom to the finite upper abutment stage. -/
noncomputable abbrev horizontalCanonicalAbutmentTotalMap (p q : ℕ) :
    (⊥ : EInt) ⟶ horizontalAbutmentUpperIndex p q :=
  homOfLE bot_le

/-- Composition formula for the lower two filtration maps. -/
theorem horizontalCanonicalAbutmentLower_comp_middle (p : ℕ) :
    horizontalCanonicalAbutmentLowerMap p ≫
        horizontalCanonicalAbutmentMiddleMap p =
      horizontalCanonicalAbutmentLowerCompositeMap p :=
  Subsingleton.elim _ _

/-- Composition formula from bottom through stage `p` to the upper stage. -/
theorem horizontalCanonicalAbutmentLowerComposite_comp_upper
    (p q : ℕ) :
    horizontalCanonicalAbutmentLowerCompositeMap p ≫
        horizontalCanonicalAbutmentUpperMap p q =
      horizontalCanonicalAbutmentTotalMap p q :=
  Subsingleton.elim _ _

/-- Map on relative homology induced by the inclusion of stage `p-1` into
stage `p`. -/
noncomputable abbrev horizontalCanonicalAbutmentPreviousHomologyMap
    (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q : ℕ) : ℤ))).obj
        (mk₁ (horizontalCanonicalAbutmentLowerMap p)) ⟶
      ((horizontalCompleteFiltrationSpectralObject K).H
        (-((p + q : ℕ) : ℤ))).obj
          (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) :=
  ((horizontalCompleteFiltrationSpectralObject K).H
    (-((p + q : ℕ) : ℤ))).map
      (twoδ₂Toδ₁
        (horizontalCanonicalAbutmentLowerMap p)
        (horizontalCanonicalAbutmentMiddleMap p)
        (horizontalCanonicalAbutmentLowerCompositeMap p)
        (horizontalCanonicalAbutmentLower_comp_middle p))

/-- Connecting morphism from upper relative homology into stage-`p`
homology. -/
noncomputable abbrev horizontalCanonicalAbutmentBoundaryMap
    (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q + 1 : ℕ) : ℤ))).obj
        (mk₁ (horizontalCanonicalAbutmentUpperMap p q)) ⟶
      ((horizontalCompleteFiltrationSpectralObject K).H
        (-((p + q : ℕ) : ℤ))).obj
          (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) :=
  (horizontalCompleteFiltrationSpectralObject K).δ
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)

/-- Map from stage-`p` homology into homology of the finite upper stage. -/
noncomputable abbrev horizontalCanonicalAbutmentToUpperHomologyMap
    (p q : ℕ) :
    ((horizontalCompleteFiltrationSpectralObject K).H
      (-((p + q : ℕ) : ℤ))).obj
        (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ⟶
      ((horizontalCompleteFiltrationSpectralObject K).H
        (-((p + q : ℕ) : ℤ))).obj
          (mk₁ (horizontalCanonicalAbutmentTotalMap p q)) :=
  ((horizontalCompleteFiltrationSpectralObject K).H
    (-((p + q : ℕ) : ℤ))).map
      (twoδ₂Toδ₁
        (horizontalCanonicalAbutmentLowerCompositeMap p)
        (horizontalCanonicalAbutmentUpperMap p q)
        (horizontalCanonicalAbutmentTotalMap p q)
        (horizontalCanonicalAbutmentLowerComposite_comp_upper p q))

/-- The connecting morphism followed by the upper-stage homology map is
zero. -/
theorem horizontalCanonicalAbutmentBoundary_comp_toUpper (p q : ℕ) :
    horizontalCanonicalAbutmentBoundaryMap K p q ≫
      horizontalCanonicalAbutmentToUpperHomologyMap K p q = 0 :=
  (horizontalCompleteFiltrationSpectralObject K).zero₁
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (horizontalCanonicalAbutmentTotalMap p q)
    (horizontalCanonicalAbutmentLowerComposite_comp_upper p q)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)

/-- Exactness at stage-`p` homology in the long homology sequence. -/
theorem horizontalCanonicalAbutmentBoundaryToUpper_exact (p q : ℕ) :
    (ShortComplex.mk
      (horizontalCanonicalAbutmentBoundaryMap K p q)
      (horizontalCanonicalAbutmentToUpperHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundary_comp_toUpper K p q)).Exact :=
  (horizontalCompleteFiltrationSpectralObject K).exact₁
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (horizontalCanonicalAbutmentTotalMap p q)
    (horizontalCanonicalAbutmentLowerComposite_comp_upper p q)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega)

/-- Cokernel presentation of the canonical finite abutment term. -/
noncomputable abbrev horizontalCanonicalAbutmentCokernelSequence
    (p q : ℕ) : ShortComplex C :=
  (horizontalCompleteFiltrationSpectralObject K).cokernelSequenceE
    (horizontalCanonicalAbutmentLowerMap p)
    (horizontalCanonicalAbutmentMiddleMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentLower_comp_middle p)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
      (-((p + q : ℕ) : ℤ) + 1)

/-- Exactness of the canonical abutment cokernel presentation. -/
theorem horizontalCanonicalAbutmentCokernelSequence_exact (p q : ℕ) :
    (horizontalCanonicalAbutmentCokernelSequence K p q).Exact :=
  (horizontalCompleteFiltrationSpectralObject K).cokernelSequenceE_exact
    (horizontalCanonicalAbutmentLowerMap p)
    (horizontalCanonicalAbutmentMiddleMap p)
    (horizontalCanonicalAbutmentUpperMap p q)
    (horizontalCanonicalAbutmentLowerCompositeMap p)
    (horizontalCanonicalAbutmentLower_comp_middle p)
    (-((p + q + 1 : ℕ) : ℤ)) (-((p + q : ℕ) : ℤ))
      (-((p + q : ℕ) : ℤ) + 1)

/-- The cokernel of the two incoming maps is the canonical finite abutment
term. -/
noncomputable def horizontalCanonicalAbutmentCokernelIso (p q : ℕ) :
    cokernel (biprod.desc
      (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundaryMap K p q)) ≅
      horizontalFirstQuadrantCanonicalAbutmentTerm K p q := by
  let S := horizontalCanonicalAbutmentCokernelSequence K p q
  have hS : S.Exact :=
    horizontalCanonicalAbutmentCokernelSequence_exact K p q
  have hg : Epi S.g := by
    dsimp [S, horizontalCanonicalAbutmentCokernelSequence]
    infer_instance
  let _ := hg
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel S.f) hS.gIsCokernel

/-- Quotient of the stage-`p` image by the stage-`p-1` image inside finite
upper-stage homology. -/
noncomputable abbrev horizontalCanonicalAbutmentImageQuotient
    (p q : ℕ) : C :=
  cokernel (CategoryTheory.imageCompMap
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
    (horizontalCanonicalAbutmentToUpperHomologyMap K p q))

/-- The canonical finite abutment term is the quotient of the two nested
images in finite upper-stage homology. -/
noncomputable def horizontalCanonicalAbutmentImageQuotientIso
    (p q : ℕ) :
    horizontalFirstQuadrantCanonicalAbutmentTerm K p q ≅
      horizontalCanonicalAbutmentImageQuotient K p q :=
  (horizontalCanonicalAbutmentCokernelIso K p q).symm ≪≫
    CategoryTheory.imageQuotientBiprodIso
      (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundaryMap K p q)
      (horizontalCanonicalAbutmentToUpperHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundary_comp_toUpper K p q)
      (horizontalCanonicalAbutmentBoundaryToUpper_exact K p q)

end HomologicalComplex₂
